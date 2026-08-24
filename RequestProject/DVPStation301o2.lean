import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationHalfEval

/-!
# Station `t = 301/2` (rung-154.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT301o2 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((301 : ℕ) : ℝ) * (Real.log ((n : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))

theorem st301o2_c1 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((499983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((0 : ℚ) : ℝ) ≤ Real.log ((1 : ℕ)) / 2 := by
    have h := (log_br_1).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((1 : ℕ)) / 2 ≤ ((0 : ℚ) : ℝ) := by
    have h := (log_br_1).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -641/312500) (δ := 201/1000000000) (ψ := 1641/200000) 301 0
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t1 : ((249979/250000 : ℚ) : ℝ) ≤ stT301o2 1 := by
  have hc : ((249979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249979/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((249979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c2 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-401679/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log ((2 : ℕ)) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((2 : ℕ)) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6259273/10000000) (δ := 7579/1000000000) (ψ := 1641/200000) 301 17
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t2 : ((-88764884371/156250000000 : ℚ) : ℝ) ≤ stT301o2 2 := by
  have hc : ((-50213/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88764884371/156250000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-50213/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c3 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-97199/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log ((3 : ℕ)) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((3 : ℕ)) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2462651/5000000) (δ := 961/125000000) (ψ := 1641/200000) 301 26
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t3 : ((-1122501773769/5000000000000 : ℚ) : ℝ) ≤ stT301o2 3 := by
  have hc : ((-194423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1122501773769/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-194423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c4 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((2829/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log ((4 : ℕ)) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((4 : ℕ)) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3209949/10000000) (δ := 1897/250000000) (ψ := 1641/200000) 301 33
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t4 : ((5657/40000 : ℚ) : ℝ) ≤ stT301o2 4 := by
  have hc : ((5657/20000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5657/40000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((5657/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c5 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-59529/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log ((5 : ℕ)) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((5 : ℕ)) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7080051/10000000) (δ := 477/62500000) (ψ := 1641/200000) 301 39
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t5 : ((-266235759369/625000000000 : ℚ) : ℝ) ≤ stT301o2 5 := by
  have hc : ((-476257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-266235759369/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-476257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c6 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((173027/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log ((6 : ℕ)) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((6 : ℕ)) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -8209/62500) (δ := 7543/1000000000) (ψ := 1641/200000) 301 43
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t6 : ((353169394097/1000000000000 : ℚ) : ℝ) ≤ stT301o2 6 := by
  have hc : ((173017/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((353169394097/1000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((173017/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c7 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-24237/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log ((7 : ℕ)) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((7 : ℕ)) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1536523/2500000) (δ := 7589/1000000000) (ψ := 1641/200000) 301 47
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t7 : ((-293162116993/1000000000000 : ℚ) : ℝ) ≤ stT301o2 7 := by
  have hc : ((-387817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-293162116993/1000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-387817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c8 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((351599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log ((8 : ℕ)) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((8 : ℕ)) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3028793/10000000) (δ := 7643/1000000000) (ψ := 1641/200000) 301 50
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t8 : ((1242913090617/10000000000000 : ℚ) : ℝ) ≤ stT301o2 8 := by
  have hc : ((351549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1242913090617/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((351549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c9 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-691769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log ((9 : ℕ)) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((9 : ℕ)) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5836829/10000000) (δ := 7621/1000000000) (ψ := 1641/200000) 301 53
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t9 : ((-1153031897273/5000000000000 : ℚ) : ℝ) ≤ stT301o2 9 := by
  have hc : ((-691819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1153031897273/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-691819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c10 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((23083/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log ((10 : ℕ)) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((10 : ℕ)) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2389133/10000000) (δ := 1899/250000000) (ψ := 1641/200000) 301 55
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t10 : ((72988515437/400000000000 : ℚ) : ℝ) ≤ stT301o2 10 := by
  have hc : ((23081/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72988515437/400000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((23081/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c11 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-917867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log ((11 : ℕ)) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((11 : ℕ)) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6833669/10000000) (δ := 3771/500000000) (ψ := 1641/200000) 301 57
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t11 : ((-1383812198769/5000000000000 : ℚ) : ℝ) ≤ stT301o2 11 := by
  have hc : ((-917917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1383812198769/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-917917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c12 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-496361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log ((12 : ℕ)) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((12 : ℕ)) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3776091/5000000) (δ := 7721/1000000000) (ψ := 1641/200000) 301 60
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t12 : ((-22389738723/78125000000 : ℚ) : ℝ) ≤ stT301o2 12 := by
  have hc : ((-248193/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22389738723/78125000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-248193/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c13 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-921363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log ((13 : ℕ)) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((13 : ℕ)) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6855921/10000000) (δ := 1891/250000000) (ψ := 1641/200000) 301 61
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t13 : ((-2555539876913/10000000000000 : ℚ) : ℝ) ≤ stT301o2 13 := by
  have hc : ((-921413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2555539876913/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-921413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c14 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((119601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log ((14 : ℕ)) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((14 : ℕ)) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 332313/1000000) (δ := 963/125000000) (ψ := 1641/200000) 301 63
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t14 : ((9986882891/156250000000 : ℚ) : ℝ) ≤ stT301o2 14 := by
  have hc : ((14947/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9986882891/156250000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((14947/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c15 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((657209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log ((15 : ℕ)) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((15 : ℕ)) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1067109/5000000) (δ := 1917/250000000) (ψ := 1641/200000) 301 65
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t15 : ((424194163023/2500000000000 : ℚ) : ℝ) ≤ stT301o2 15 := by
  have hc : ((657159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((424194163023/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((657159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c16 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-844363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log ((16 : ℕ)) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((16 : ℕ)) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6440429/10000000) (δ := 941/125000000) (ψ := 1641/200000) 301 66
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t16 : ((-2111033344413/10000000000000 : ℚ) : ℝ) ≤ stT301o2 16 := by
  have hc : ((-844413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2111033344413/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-844413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c17 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((647729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log ((17 : ℕ)) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((17 : ℕ)) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -541373/2500000) (δ := 7613/1000000000) (ψ := 1641/200000) 301 68
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t17 : ((392713037181/2500000000000 : ℚ) : ℝ) ≤ stT301o2 17 := by
  have hc : ((647679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((392713037181/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((647679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c18 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((117567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log ((18 : ℕ)) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((18 : ℕ)) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3632393/10000000) (δ := 7547/1000000000) (ψ := 1641/200000) 301 69
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t18 : ((138495077187/5000000000000 : ℚ) : ℝ) ≤ stT301o2 18 := by
  have hc : ((117517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138495077187/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((117517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c19 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-98637/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log ((19 : ℕ)) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((19 : ℕ)) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -29763/40000) (δ := 1923/250000000) (ψ := 1641/200000) 301 71
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t19 : ((-56575083359/250000000000 : ℚ) : ℝ) ≤ stT301o2 19 := by
  have hc : ((-49321/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56575083359/250000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-49321/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c20 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((7737/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log ((20 : ℕ)) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((20 : ℕ)) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3849609/10000000) (δ := 1527/200000000) (ψ := 1641/200000) 301 72
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t20 : ((34544999083/5000000000000 : ℚ) : ℝ) ≤ stT301o2 20 := by
  have hc : ((15449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34544999083/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((15449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c21 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((886947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log ((21 : ℕ)) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((21 : ℕ)) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1200259/10000000) (δ := 3813/500000000) (ψ := 1641/200000) 301 73
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t21 : ((967683560833/5000000000000 : ℚ) : ℝ) ≤ stT301o2 21 := by
  have hc : ((886897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((967683560833/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((886897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c22 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((485909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log ((22 : ℕ)) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((22 : ℕ)) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 594927/10000000) (δ := 193/25000000) (ψ := 1641/200000) 301 74
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t22 : ((258977022297/1250000000000 : ℚ) : ℝ) ≤ stT301o2 22 := by
  have hc : ((121471/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258977022297/1250000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((121471/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c23 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((799231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log ((23 : ℕ)) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((23 : ℕ)) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 805977/5000000) (δ := 377/50000000) (ψ := 1641/200000) 301 75
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t23 : ((208300933383/1250000000000 : ℚ) : ℝ) ≤ stT301o2 23 := by
  have hc : ((799181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208300933383/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((799181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c24 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((180031/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log ((24 : ℕ)) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((24 : ℕ)) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 23963/125000) (δ := 3803/500000000) (ψ := 1641/200000) 301 76
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t24 : ((734922285917/5000000000000 : ℚ) : ℝ) ≤ stT301o2 24 := by
  have hc : ((360037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((734922285917/5000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((360037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c25 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((809591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log ((25 : ℕ)) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((25 : ℕ)) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 784177/5000000) (δ := 7699/1000000000) (ψ := 1641/200000) 301 77
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t25 : ((809541/5000000 : ℚ) : ℝ) ≤ stT301o2 25 := by
  have hc : ((809541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((809541/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((809541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c26 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((484841/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log ((26 : ℕ)) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((26 : ℕ)) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 30859/500000) (δ := 241/31250000) (ψ := 1641/200000) 301 78
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t26 : ((59425139461/312500000000 : ℚ) : ℝ) ≤ stT301o2 26 := by
  have hc : ((30301/31250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59425139461/312500000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((30301/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c27 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((23429/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log ((27 : ℕ)) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((27 : ℕ)) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -222749/2500000) (δ := 237/31250000) (ψ := 1641/200000) 301 79
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t27 : ((360693639/2000000000 : ℚ) : ℝ) ≤ stT301o2 27 := by
  have hc : ((93711/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((360693639/2000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((93711/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c28 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((393607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log ((28 : ℕ)) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((28 : ℕ)) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -728903/2500000) (δ := 7527/1000000000) (ψ := 1641/200000) 301 80
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t28 : ((371876338427/5000000000000 : ℚ) : ℝ) ≤ stT301o2 28 := by
  have hc : ((393557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((371876338427/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((393557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c29 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-562489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log ((29 : ℕ)) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((29 : ℕ)) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2710237/5000000) (δ := 767/100000000) (ψ := 1641/200000) 301 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t29 : ((-522304523103/5000000000000 : ℚ) : ℝ) ≤ stT301o2 29 := by
  have hc : ((-562539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-522304523103/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-562539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c30 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-978527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log ((30 : ℕ)) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((30 : ℕ)) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3667483/5000000) (δ := 7633/1000000000) (ψ := 1641/200000) 301 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t30 : ((-893314564567/5000000000000 : ℚ) : ℝ) ≤ stT301o2 30 := by
  have hc : ((-978577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-893314564567/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-978577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c31 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-3721/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log ((31 : ℕ)) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((31 : ℕ)) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1982101/5000000) (δ := 7663/1000000000) (ψ := 1641/200000) 301 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t31 : ((-6705567609/2500000000000 : ℚ) : ℝ) ≤ stT301o2 31 := by
  have hc : ((-7467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6705567609/2500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-7467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c32 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((249187/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log ((32 : ℕ)) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((32 : ℕ)) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 201687/10000000) (δ := 3853/500000000) (ψ := 1641/200000) 301 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t32 : ((440482209167/2500000000000 : ℚ) : ℝ) ≤ stT301o2 32 := by
  have hc : ((498349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((440482209167/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((498349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c33 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-147/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log ((33 : ℕ)) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((33 : ℕ)) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3928461/10000000) (δ := 1531/200000000) (ψ := 1641/200000) 301 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t33 : ((-555307863/5000000000000 : ℚ) : ℝ) ≤ stT301o2 33 := by
  have hc : ((-319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-555307863/5000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c34 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-7807/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log ((34 : ℕ)) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((34 : ℕ)) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 730373/1000000) (δ := 1511/200000000) (ψ := 1641/200000) 301 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t34 : ((-33473954241/200000000000 : ℚ) : ℝ) ≤ stT301o2 34 := by
  have hc : ((-39037/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33473954241/200000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-39037/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c35 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((539523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log ((35 : ℕ)) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((35 : ℕ)) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1251157/5000000) (δ := 241/31250000) (ψ := 1641/200000) 301 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t35 : ((227968881921/2500000000000 : ℚ) : ℝ) ≤ stT301o2 35 := by
  have hc : ((539473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227968881921/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((539473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c36 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((126007/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log ((36 : ℕ)) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((36 : ℕ)) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2606349/10000000) (δ := 1921/250000000) (ψ := 1641/200000) 301 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t36 : ((209990749337/2500000000000 : ℚ) : ℝ) ≤ stT301o2 36 := by
  have hc : ((251989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209990749337/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((251989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c37 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-199633/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log ((37 : ℕ)) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((37 : ℕ)) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 308101/400000) (δ := 237/31250000) (ψ := 1641/200000) 301 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t37 : ((-32821109557/200000000000 : ℚ) : ℝ) ≤ stT301o2 37 := by
  have hc : ((-199643/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32821109557/200000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-199643/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c38 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((172123/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log ((38 : ℕ)) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((38 : ℕ)) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 253559/1250000) (δ := 7577/1000000000) (ψ := 1641/200000) 301 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t38 : ((279200062647/2500000000000 : ℚ) : ℝ) ≤ stT301o2 38 := by
  have hc : ((344221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((279200062647/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((344221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c39 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((8313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log ((39 : ℕ)) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((39 : ℕ)) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3906209/10000000) (δ := 7633/1000000000) (ψ := 1641/200000) 301 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t39 : ((13231384903/10000000000000 : ℚ) : ℝ) ≤ stT301o2 39 := by
  have hc : ((8263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13231384903/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((8263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c40 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-9789/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log ((40 : ℕ)) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((40 : ℕ)) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5619613/10000000) (δ := 7533/1000000000) (ψ := 1641/200000) 301 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t40 : ((-495328157947/5000000000000 : ℚ) : ℝ) ≤ stT301o2 40 := by
  have hc : ((-313273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-495328157947/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-313273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c41 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((949517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log ((41 : ℕ)) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((41 : ℕ)) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2493/31250) (δ := 7713/1000000000) (ψ := 1641/200000) 301 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t41 : ((1482817744179/10000000000000 : ℚ) : ℝ) ≤ stT301o2 41 := by
  have hc : ((949467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1482817744179/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((949467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c42 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-197251/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log ((42 : ℕ)) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((42 : ℕ)) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7439001/10000000) (δ := 1521/200000000) (ψ := 1641/200000) 301 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t42 : ((-152190214937/1000000000000 : ℚ) : ℝ) ≤ stT301o2 42 := by
  have hc : ((-197261/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152190214937/1000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-197261/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c43 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((26381/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log ((43 : ℕ)) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((43 : ℕ)) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 28287/200000) (δ := 3799/500000000) (ψ := 1641/200000) 301 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t43 : ((128730388787/1000000000000 : ℚ) : ℝ) ≤ stT301o2 43 := by
  have hc : ((422071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128730388787/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((422071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c44 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-634011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log ((44 : ℕ)) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((44 : ℕ)) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2821907/5000000) (δ := 1511/200000000) (ψ := 1641/200000) 301 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t44 : ((-955883098977/10000000000000 : ℚ) : ℝ) ≤ stT301o2 44 := by
  have hc : ((-634061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-955883098977/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-634061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c45 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((43151/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log ((45 : ℕ)) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((45 : ℕ)) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2811577/10000000) (δ := 1511/200000000) (ψ := 1641/200000) 301 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t45 : ((32159108403/500000000000 : ℚ) : ℝ) ≤ stT301o2 45 := by
  have hc : ((21573/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32159108403/500000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((21573/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c46 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-69073/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log ((46 : ℕ)) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((46 : ℕ)) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -185073/400000) (δ := 1903/250000000) (ψ := 1641/200000) 301 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t46 : ((-10186104291/250000000000 : ℚ) : ℝ) ≤ stT301o2 46 := by
  have hc : ((-138171/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10186104291/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-138171/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c47 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((91889/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log ((47 : ℕ)) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((47 : ℕ)) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 86623/250000) (δ := 7591/1000000000) (ψ := 1641/200000) 301 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t47 : ((16749666467/625000000000 : ℚ) : ℝ) ≤ stT301o2 47 := by
  have hc : ((11483/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16749666467/625000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((11483/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c48 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-157229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log ((48 : ℕ)) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((48 : ℕ)) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4321701/10000000) (δ := 7669/1000000000) (ψ := 1641/200000) 301 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t48 : ((-14188295869/625000000000 : ℚ) : ℝ) ≤ stT301o2 48 := by
  have hc : ((-157279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14188295869/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-157279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c49 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((195029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log ((49 : ℕ)) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((49 : ℕ)) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3436273/10000000) (δ := 7669/1000000000) (ψ := 1641/200000) 301 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t49 : ((278541345009/10000000000000 : ℚ) : ℝ) ≤ stT301o2 49 := by
  have hc : ((194979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((278541345009/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((194979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c50 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-73249/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log ((50 : ℕ)) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((50 : ℕ)) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4670387/10000000) (δ := 947/125000000) (ψ := 1641/200000) 301 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t50 : ((-103607438961/2500000000000 : ℚ) : ℝ) ≤ stT301o2 50 := by
  have hc : ((-146523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103607438961/2500000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-146523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c51 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((442747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log ((51 : ℕ)) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((51 : ℕ)) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2780341/10000000) (δ := 7577/1000000000) (ψ := 1641/200000) 301 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t51 : ((15497493879/250000000000 : ℚ) : ℝ) ≤ stT301o2 51 := by
  have hc : ((442697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15497493879/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((442697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c52 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-627103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log ((52 : ℕ)) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((52 : ℕ)) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2810781/5000000) (δ := 3767/500000000) (ψ := 1641/200000) 301 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t52 : ((-869705049903/10000000000000 : ℚ) : ℝ) ≤ stT301o2 52 := by
  have hc : ((-627153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-869705049903/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-627153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c53 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((203741/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log ((53 : ℕ)) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((53 : ℕ)) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1545323/10000000) (δ := 7619/1000000000) (ψ := 1641/200000) 301 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t53 : ((111936994497/1000000000000 : ℚ) : ℝ) ≤ stT301o2 53 := by
  have hc : ((407457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111936994497/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((407457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c54 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-95833/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log ((54 : ℕ)) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((54 : ℕ)) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7129737/10000000) (δ := 7691/1000000000) (ψ := 1641/200000) 301 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t54 : ((-16302379233/125000000000 : ℚ) : ℝ) ≤ stT301o2 54 := by
  have hc : ((-47919/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16302379233/125000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-47919/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c55 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((995921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log ((55 : ℕ)) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((55 : ℕ)) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -225889/10000000) (δ := 241/31250000) (ψ := 1641/200000) 301 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t55 : ((1342831460529/10000000000000 : ℚ) : ℝ) ≤ stT301o2 55 := by
  have hc : ((995871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1342831460529/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((995871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c56 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-433869/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log ((56 : ℕ)) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((56 : ℕ)) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1638393/2500000) (δ := 3781/500000000) (ψ := 1641/200000) 301 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t56 : ((-289907794729/2500000000000 : ℚ) : ℝ) ≤ stT301o2 56 := by
  have hc : ((-216947/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-289907794729/2500000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-216947/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c57 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((135503/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log ((57 : ℕ)) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((57 : ℕ)) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2494917/10000000) (δ := 1531/200000000) (ψ := 1641/200000) 301 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t57 : ((89730751473/1250000000000 : ℚ) : ℝ) ≤ stT301o2 57 := by
  have hc : ((270981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89730751473/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((270981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c58 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-12171/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log ((58 : ℕ)) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((58 : ℕ)) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1012187/2500000) (δ := 1511/200000000) (ψ := 1641/200000) 301 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t58 : ((-6399090971/1000000000000 : ℚ) : ℝ) ≤ stT301o2 58 := by
  have hc : ((-24367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6399090971/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-24367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c59 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-248519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log ((59 : ℕ)) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((59 : ℕ)) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5227447/10000000) (δ := 1521/200000000) (ψ := 1641/200000) 301 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t59 : ((-1011177963/15625000000 : ℚ) : ℝ) ≤ stT301o2 59 := by
  have hc : ((-7767/15625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1011177963/15625000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-7767/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c60 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((452697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log ((60 : ℕ)) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((60 : ℕ)) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 34257/312500) (δ := 3799/500000000) (ψ := 1641/200000) 301 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t60 : ((4565600281/39062500000 : ℚ) : ℝ) ≤ stT301o2 60 := by
  have hc : ((14146/15625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4565600281/39062500000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((14146/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c61 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-488441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log ((61 : ℕ)) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((61 : ℕ)) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7315373/10000000) (δ := 239/31250000) (ψ := 1641/200000) 301 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t61 : ((-312708361977/2500000000000 : ℚ) : ℝ) ≤ stT301o2 61 := by
  have hc : ((-244233/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-312708361977/2500000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-244233/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c62 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((613879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log ((62 : ℕ)) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((62 : ℕ)) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2274577/10000000) (δ := 7591/1000000000) (ψ := 1641/200000) 301 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t62 : ((779563443829/10000000000000 : ℚ) : ℝ) ≤ stT301o2 62 := by
  have hc : ((613829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((779563443829/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((613829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c63 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((72503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log ((63 : ℕ)) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((63 : ℕ)) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1872787/5000000) (δ := 3831/500000000) (ψ := 1641/200000) 301 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t63 : ((91282158093/10000000000000 : ℚ) : ℝ) ≤ stT301o2 63 := by
  have hc : ((72453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91282158093/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((72453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c64 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-373667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log ((64 : ℕ)) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((64 : ℕ)) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1509273/2500000) (δ := 3817/500000000) (ψ := 1641/200000) 301 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t64 : ((-116778843423/1250000000000 : ℚ) : ℝ) ≤ stT301o2 64 := by
  have hc : ((-93423/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116778843423/1250000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-93423/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c65 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((249171/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log ((65 : ℕ)) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((65 : ℕ)) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -50909/2500000) (δ := 7719/1000000000) (ψ := 1641/200000) 301 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t65 : ((618085995999/5000000000000 : ℚ) : ℝ) ≤ stT301o2 65 := by
  have hc : ((498317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((618085995999/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((498317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c66 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-150401/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log ((66 : ℕ)) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((66 : ℕ)) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 138519/250000) (δ := 1921/250000000) (ψ := 1641/200000) 301 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t66 : ((-74058493341/1000000000000 : ℚ) : ℝ) ≤ stT301o2 66 := by
  have hc : ((-300827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74058493341/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-300827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c67 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-115391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log ((67 : ℕ)) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((67 : ℕ)) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4509193/10000000) (δ := 7527/1000000000) (ψ := 1641/200000) 301 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t67 : ((-3525078753/125000000000 : ℚ) : ℝ) ≤ stT301o2 67 := by
  have hc : ((-14427/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3525078753/125000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-14427/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c68 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((227657/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log ((68 : ℕ)) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((68 : ℕ)) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 266247/2500000) (δ := 1919/250000000) (ψ := 1641/200000) 301 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t68 : ((276059476971/2500000000000 : ℚ) : ℝ) ≤ stT301o2 68 := by
  have hc : ((455289/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((276059476971/2500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((455289/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c69 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-434287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log ((69 : ℕ)) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((69 : ℕ)) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6557787/10000000) (δ := 7577/1000000000) (ψ := 1641/200000) 301 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t69 : ((-65356301251/625000000000 : ℚ) : ℝ) ≤ stT301o2 69 := by
  have hc : ((-54289/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65356301251/625000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-54289/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c70 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((76151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log ((70 : ℕ)) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((70 : ℕ)) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -934107/2500000) (δ := 3767/500000000) (ψ := 1641/200000) 301 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t70 : ((22739511507/2500000000000 : ℚ) : ℝ) ≤ stT301o2 70 := by
  have hc : ((76101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22739511507/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((76101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c71 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((80197/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log ((71 : ℕ)) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((71 : ℕ)) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 100033/625000) (δ := 3817/500000000) (ψ := 1641/200000) 301 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t71 : ((1487036593/15625000000 : ℚ) : ℝ) ≤ stT301o2 71 := by
  have hc : ((2506/3125 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1487036593/15625000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((2506/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c72 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-23061/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log ((72 : ℕ)) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((72 : ℕ)) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6862873/10000000) (δ := 7569/1000000000) (ψ := 1641/200000) 301 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t72 : ((-6794784593/62500000000 : ℚ) : ℝ) ≤ stT301o2 72 := by
  have hc : ((-92249/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6794784593/62500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-92249/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c73 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((54219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log ((73 : ℕ)) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((73 : ℕ)) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3655361/10000000) (δ := 7541/1000000000) (ψ := 1641/200000) 301 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t73 : ((31714626867/2500000000000 : ℚ) : ℝ) ≤ stT301o2 73 := by
  have hc : ((27097/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31714626867/2500000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((27097/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c74 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((833437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log ((74 : ℕ)) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((74 : ℕ)) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 731873/5000000) (δ := 7541/1000000000) (ψ := 1641/200000) 301 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t74 : ((242198096553/2500000000000 : ℚ) : ℝ) ≤ stT301o2 74 := by
  have hc : ((833387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242198096553/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((833387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c75 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-4299/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log ((75 : ℕ)) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((75 : ℕ)) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6514187/10000000) (δ := 3831/500000000) (ψ := 1641/200000) 301 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t75 : ((-19857393097/200000000000 : ℚ) : ℝ) ≤ stT301o2 75 := by
  have hc : ((-17197/20000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19857393097/200000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-17197/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c76 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-113069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log ((76 : ℕ)) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((76 : ℕ)) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4210269/10000000) (δ := 3849/500000000) (ψ := 1641/200000) 301 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t76 : ((-129756429401/10000000000000 : ℚ) : ℝ) ≤ stT301o2 76 := by
  have hc : ((-113119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129756429401/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-113119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c77 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((480077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log ((77 : ℕ)) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((77 : ℕ)) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 177027/2500000) (δ := 1521/200000000) (ψ := 1641/200000) 301 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t77 : ((27353482973/250000000000 : ℚ) : ℝ) ≤ stT301o2 77 := by
  have hc : ((120013/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27353482973/250000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((120013/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c78 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-60869/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log ((78 : ℕ)) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((78 : ℕ)) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1390753/2500000) (δ := 1541/200000000) (ψ := 1641/200000) 301 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t78 : ((-17231572743/250000000000 : ℚ) : ℝ) ≤ stT301o2 78 := by
  have hc : ((-30437/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17231572743/250000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-30437/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c79 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-269801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log ((79 : ℕ)) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((79 : ℕ)) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2675951/5000000) (δ := 1511/200000000) (ψ := 1641/200000) 301 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t79 : ((-4743406167/78125000000 : ℚ) : ℝ) ≤ stT301o2 79 := by
  have hc : ((-134913/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4743406167/78125000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-134913/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c80 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((969491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log ((80 : ℕ)) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((80 : ℕ)) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -619129/10000000) (δ := 3849/500000000) (ψ := 1641/200000) 301 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t80 : ((1083867029553/10000000000000 : ℚ) : ℝ) ≤ stT301o2 80 := by
  have hc : ((969441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1083867029553/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((969441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c81 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-12779/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log ((81 : ℕ)) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((81 : ℕ)) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4054837/10000000) (δ := 1887/250000000) (ψ := 1641/200000) 301 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t81 : ((-3553197287/625000000000 : ℚ) : ℝ) ≤ stT301o2 81 := by
  have hc : ((-25583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3553197287/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-25583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c82 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-947013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log ((82 : ℕ)) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((82 : ℕ)) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7036501/10000000) (δ := 7563/1000000000) (ψ := 1641/200000) 301 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t82 : ((-261464205977/2500000000000 : ℚ) : ℝ) ≤ stT301o2 82 := by
  have hc : ((-947063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261464205977/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-947063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c83 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((274207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log ((83 : ℕ)) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((83 : ℕ)) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -154739/625000) (δ := 7663/1000000000) (ψ := 1641/200000) 301 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t83 : ((75238419711/1250000000000 : ℚ) : ℝ) ≤ stT301o2 83 := by
  have hc : ((137091/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75238419711/1250000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((137091/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c84 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((68799/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log ((84 : ℕ)) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((84 : ℕ)) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1015101/5000000) (δ := 1509/100000000) (ψ := 1641/200000) 301 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t84 : ((37530188333/500000000000 : ℚ) : ℝ) ≤ stT301o2 84 := by
  have hc : ((34397/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37530188333/500000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((34397/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c85 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-426673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log ((85 : ℕ)) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((85 : ℕ)) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3241457/5000000) (δ := 7563/1000000000) (ψ := 1641/200000) 301 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t85 : ((-231409632897/2500000000000 : ℚ) : ℝ) ≤ stT301o2 85 := by
  have hc : ((-213349/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-231409632897/2500000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-213349/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c86 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-70263/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log ((86 : ℕ)) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((86 : ℕ)) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4824429/10000000) (δ := 767/100000000) (ψ := 1641/200000) 301 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t86 : ((-9472167943/250000000000 : ℚ) : ℝ) ≤ stT301o2 86 := by
  have hc : ((-70273/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9472167943/250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-70273/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c87 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((982031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log ((87 : ℕ)) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((87 : ℕ)) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -474641/10000000) (δ := 7633/1000000000) (ψ := 1641/200000) 301 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t87 : ((65799600867/625000000000 : ℚ) : ℝ) ≤ stT301o2 87 := by
  have hc : ((981981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65799600867/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((981981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c88 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((20311/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log ((88 : ℕ)) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((88 : ℕ)) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 29886/78125) (δ := 767/100000000) (ψ := 1641/200000) 301 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t88 : ((10812468429/2500000000000 : ℚ) : ℝ) ≤ stT301o2 88 := by
  have hc : ((10143/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10812468429/2500000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((10143/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c89 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-996029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log ((89 : ℕ)) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((89 : ℕ)) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7631119/10000000) (δ := 3813/500000000) (ψ := 1641/200000) 301 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t89 : ((-527920873921/5000000000000 : ℚ) : ℝ) ≤ stT301o2 89 := by
  have hc : ((-996079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-527920873921/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-996079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c90 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((198601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log ((90 : ℕ)) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((90 : ℕ)) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -685433/2000000) (δ := 1919/250000000) (ψ := 1641/200000) 301 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t90 : ((52322755173/2500000000000 : ℚ) : ℝ) ≤ stT301o2 90 := by
  have hc : ((198551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52322755173/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((198551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c91 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((957631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log ((91 : ℕ)) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((91 : ℕ)) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 730341/10000000) (δ := 7613/500000000) (ψ := 1641/200000) 301 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t91 : ((250954210251/2500000000000 : ℚ) : ℝ) ≤ stT301o2 91 := by
  have hc : ((957581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250954210251/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((957581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c92 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-71607/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log ((92 : ℕ)) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((92 : ℕ)) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1210599/2500000) (δ := 3863/500000000) (ψ := 1641/200000) 301 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t92 : ((-74665950541/2000000000000 : ℚ) : ℝ) ≤ stT301o2 92 := by
  have hc : ((-71617/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74665950541/2000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-71617/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c93 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-182421/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log ((93 : ℕ)) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((93 : ℕ)) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3398983/5000000) (δ := 7669/1000000000) (ψ := 1641/200000) 301 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t93 : ((-23646523789/250000000000 : ℚ) : ℝ) ≤ stT301o2 93 := by
  have hc : ((-182431/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23646523789/250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-182431/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c94 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((44507/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log ((94 : ℕ)) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((94 : ℕ)) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2773859/10000000) (δ := 3767/500000000) (ψ := 1641/200000) 301 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t94 : ((22950148671/500000000000 : ℚ) : ℝ) ≤ stT301o2 94 := by
  have hc : ((22251/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22950148671/500000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((22251/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c95 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((885577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log ((95 : ℕ)) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((95 : ℕ)) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 150957/1250000) (δ := 7569/1000000000) (ψ := 1641/200000) 301 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t95 : ((454265610203/5000000000000 : ℚ) : ℝ) ≤ stT301o2 95 := by
  have hc : ((885527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454265610203/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((885527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c96 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-234517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log ((96 : ℕ)) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((96 : ℕ)) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5147483/10000000) (δ := 3817/500000000) (ψ := 1641/200000) 301 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t96 : ((-119689245291/2500000000000 : ℚ) : ℝ) ≤ stT301o2 96 := by
  have hc : ((-117271/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119689245291/2500000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-117271/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c97 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-7107/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log ((97 : ℕ)) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((97 : ℕ)) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6661477/10000000) (δ := 7541/1000000000) (ψ := 1641/200000) 301 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t97 : ((-36082386339/400000000000 : ℚ) : ℝ) ≤ stT301o2 97 := by
  have hc : ((-35537/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36082386339/400000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-35537/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c98 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((434793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log ((98 : ℕ)) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((98 : ℕ)) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2802469/10000000) (δ := 3781/500000000) (ψ := 1641/200000) 301 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t98 : ((54894563867/1250000000000 : ℚ) : ℝ) ≤ stT301o2 98 := by
  have hc : ((434743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54894563867/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((434743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c99 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((918333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log ((99 : ℕ)) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((99 : ℕ)) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 254343/2500000) (δ := 7691/1000000000) (ψ := 1641/200000) 301 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t99 : ((922908391471/10000000000000 : ℚ) : ℝ) ≤ stT301o2 99 := by
  have hc : ((918283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((922908391471/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((918283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c100 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-341697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log ((100 : ℕ)) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((100 : ℕ)) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4798797/10000000) (δ := 7541/1000000000) (ψ := 1641/200000) 301 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t100 : ((-341747/10000000 : ℚ) : ℝ) ≤ stT301o2 100 := by
  have hc : ((-341747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-341747/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-341747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c101 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-9623/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log ((101 : ℕ)) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((101 : ℕ)) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -447833/625000) (δ := 239/31250000) (ψ := 1641/200000) 301 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t101 : ((-9575748193/100000000000 : ℚ) : ℝ) ≤ stT301o2 101 := by
  have hc : ((-19247/20000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9575748193/100000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-19247/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c102 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((186341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log ((102 : ℕ)) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((102 : ℕ)) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4323/12500) (δ := 3849/500000000) (ψ := 1641/200000) 301 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t102 : ((184455474777/10000000000000 : ℚ) : ℝ) ≤ stT301o2 102 := by
  have hc : ((186291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184455474777/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((186291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c103 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((199279/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log ((103 : ℕ)) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((103 : ℕ)) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 53083/2500000) (δ := 1521/200000000) (ψ := 1641/200000) 301 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t103 : ((196345524501/2000000000000 : ℚ) : ℝ) ≤ stT301o2 103 := by
  have hc : ((199269/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196345524501/2000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((199269/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c104 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((15871/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log ((104 : ℕ)) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((104 : ℕ)) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1923811/5000000) (δ := 1511/200000000) (ψ := 1641/200000) 301 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t104 : ((388456767/125000000000 : ℚ) : ℝ) ≤ stT301o2 104 := by
  have hc : ((7923/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((388456767/125000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((7923/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c105 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-986853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log ((105 : ℕ)) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((105 : ℕ)) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3724073/5000000) (δ := 1541/200000000) (ψ := 1641/200000) 301 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t105 : ((-963119624603/10000000000000 : ℚ) : ℝ) ≤ stT301o2 105 := by
  have hc : ((-986903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-963119624603/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-986903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c106 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-150903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log ((106 : ℕ)) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((106 : ℕ)) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -293341/625000) (δ := 7547/1000000000) (ψ := 1641/200000) 301 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t106 : ((-4581070419/156250000000 : ℚ) : ℝ) ≤ stT301o2 106 := by
  have hc : ((-9433/31250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4581070419/156250000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-9433/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c107 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((223543/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log ((107 : ℕ)) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((107 : ℕ)) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -36267/312500) (δ := 7647/1000000000) (ψ := 1641/200000) 301 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t107 : ((27011872681/312500000000 : ℚ) : ℝ) ≤ stT301o2 107 := by
  have hc : ((447061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27011872681/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((447061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c108 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((29659/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log ((108 : ℕ)) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((108 : ℕ)) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 584871/2500000) (δ := 7647/1000000000) (ψ := 1641/200000) 301 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t108 : ((228295737/4000000000 : ℚ) : ℝ) ≤ stT301o2 108 := by
  have hc : ((59313/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228295737/4000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((59313/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c109 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-683171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log ((109 : ℕ)) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((109 : ℕ)) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 580723/1000000) (δ := 7547/1000000000) (ψ := 1641/200000) 301 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t109 : ((-654407520767/10000000000000 : ℚ) : ℝ) ≤ stT301o2 109 := by
  have hc : ((-683221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-654407520767/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-683221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c110 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-84951/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log ((110 : ℕ)) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((110 : ℕ)) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -646463/1000000) (δ := 7563/1000000000) (ψ := 1641/200000) 301 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t110 : ((-20250600657/250000000000 : ℚ) : ℝ) ≤ stT301o2 110 := by
  have hc : ((-21239/25000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20250600657/250000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-21239/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c111 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((68007/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log ((111 : ℕ)) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((111 : ℕ)) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -611921/2000000) (δ := 7613/1000000000) (ψ := 1641/200000) 301 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t111 : ((64539828529/2000000000000 : ℚ) : ℝ) ≤ stT301o2 111 := by
  have hc : ((67997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64539828529/2000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((67997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c112 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((992081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log ((112 : ℕ)) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((112 : ℕ)) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 314831/10000000) (δ := 7713/1000000000) (ψ := 1641/200000) 301 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t112 : ((937381004241/10000000000000 : ℚ) : ℝ) ≤ stT301o2 112 := by
  have hc : ((992031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((937381004241/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((992031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c113 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((21373/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log ((113 : ℕ)) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((113 : ℕ)) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3659317/10000000) (δ := 7613/1000000000) (ψ := 1641/200000) 301 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t113 : ((251207517/25000000000 : ℚ) : ℝ) ≤ stT301o2 113 := by
  have hc : ((21363/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251207517/25000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((21363/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c114 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-93873/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log ((114 : ℕ)) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((114 : ℕ)) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1394861/2000000) (δ := 377/50000000) (ψ := 1641/200000) 301 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t114 : ((-21981205127/250000000000 : ℚ) : ℝ) ≤ stT301o2 114 := by
  have hc : ((-46939/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21981205127/250000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-46939/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c115 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-142857/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log ((115 : ℕ)) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((115 : ℕ)) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1361901/2500000) (δ := 7683/1000000000) (ψ := 1641/200000) 301 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t115 : ((-53290609239/1000000000000 : ℚ) : ℝ) ≤ stT301o2 115 := by
  have hc : ((-285739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53290609239/1000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-285739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c116 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((640219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log ((116 : ℕ)) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((116 : ℕ)) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2190031/10000000) (δ := 757/100000000) (ψ := 1641/200000) 301 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t116 : ((148595388111/2500000000000 : ℚ) : ℝ) ≤ stT301o2 116 := by
  have hc : ((640169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148595388111/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((640169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c117 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((914773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log ((117 : ℕ)) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((117 : ℕ)) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 129953/1250000) (δ := 767/100000000) (ψ := 1641/200000) 301 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t117 : ((1691322827/20000000000 : ℚ) : ℝ) ≤ stT301o2 117 := by
  have hc : ((914723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1691322827/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((914723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c118 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-125581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log ((118 : ℕ)) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((118 : ℕ)) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 169671/400000) (δ := 193/25000000) (ψ := 1641/200000) 301 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t118 : ((-4626110313/400000000000 : ℚ) : ℝ) ≤ stT301o2 118 := by
  have hc : ((-125631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4626110313/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-125631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c119 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-492377/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log ((119 : ℕ)) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((119 : ℕ)) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7416873/10000000) (δ := 7533/1000000000) (ψ := 1641/200000) 301 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t119 : ((-225692210499/2500000000000 : ℚ) : ℝ) ≤ stT301o2 119 := by
  have hc : ((-246201/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225692210499/2500000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-246201/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c120 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-467279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log ((120 : ℕ)) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((120 : ℕ)) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5142517/10000000) (δ := 7677/1000000000) (ψ := 1641/200000) 301 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t120 : ((-426611091559/10000000000000 : ℚ) : ℝ) ≤ stT301o2 120 := by
  have hc : ((-467329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426611091559/10000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-467329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c121 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((345459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log ((121 : ℕ)) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((121 : ℕ)) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1010047/5000000) (δ := 947/125000000) (ψ := 1641/200000) 301 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t121 : ((15701529753/250000000000 : ℚ) : ℝ) ≤ stT301o2 121 := by
  have hc : ((172717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15701529753/250000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((172717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c122 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((908693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log ((122 : ℕ)) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((122 : ℕ)) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 134579/1250000) (δ := 7627/1000000000) (ψ := 1641/200000) 301 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t122 : ((822646300551/10000000000000 : ℚ) : ℝ) ≤ stT301o2 122 := by
  have hc : ((908643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((822646300551/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((908643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c123 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-44159/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log ((123 : ℕ)) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((123 : ℕ)) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4148073/10000000) (δ := 1919/250000000) (ψ := 1641/200000) 301 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t123 : ((-497992341/62500000000 : ℚ) : ℝ) ≤ stT301o2 123 := by
  have hc : ((-5523/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-497992341/62500000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-5523/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c124 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-965423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log ((124 : ℕ)) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((124 : ℕ)) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1438929/2000000) (δ := 7577/1000000000) (ψ := 1641/200000) 301 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t124 : ((-867020821771/10000000000000 : ℚ) : ℝ) ≤ stT301o2 124 := by
  have hc : ((-965473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-867020821771/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-965473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c125 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-585653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log ((125 : ℕ)) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((125 : ℕ)) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5491203/10000000) (δ := 237/31250000) (ψ := 1641/200000) 301 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t125 : ((-130967290721/2500000000000 : ℚ) : ℝ) ≤ stT301o2 125 := by
  have hc : ((-585703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130967290721/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-585703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c126 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((2713/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log ((126 : ℕ)) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((126 : ℕ)) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -155823/625000) (δ := 7569/1000000000) (ψ := 1641/200000) 301 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t126 : ((966683037/20000000000 : ℚ) : ℝ) ≤ stT301o2 126 := by
  have hc : ((10851/20000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((966683037/20000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((10851/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c127 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((981539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log ((127 : ℕ)) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((127 : ℕ)) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 240563/5000000) (δ := 3767/500000000) (ψ := 1641/200000) 301 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t127 : ((217732538271/2500000000000 : ℚ) : ℝ) ≤ stT301o2 127 := by
  have hc : ((981489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217732538271/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((981489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c128 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((98327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log ((128 : ℕ)) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((128 : ℕ)) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 343213/1000000) (δ := 3767/500000000) (ψ := 1641/200000) 301 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t128 : ((43443733333/2500000000000 : ℚ) : ℝ) ≤ stT301o2 128 := by
  have hc : ((49151/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43443733333/2500000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((49151/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c129 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-413367/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log ((129 : ℕ)) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((129 : ℕ)) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6360183/10000000) (δ := 3817/500000000) (ψ := 1641/200000) 301 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t129 : ((-22748212487/312500000000 : ℚ) : ℝ) ≤ stT301o2 129 := by
  have hc : ((-25837/31250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22748212487/312500000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-25837/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c130 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-844781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log ((130 : ℕ)) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((130 : ℕ)) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3221189/5000000) (δ := 3771/500000000) (ψ := 1641/200000) 301 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t130 : ((-740966632029/10000000000000 : ℚ) : ℝ) ≤ stT301o2 130 := by
  have hc : ((-844831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-740966632029/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-844831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c131 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((146581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log ((131 : ℕ)) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((131 : ℕ)) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -889803/2500000) (δ := 7561/1000000000) (ψ := 1641/200000) 301 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t131 : ((16003090103/1250000000000 : ℚ) : ℝ) ≤ stT301o2 131 := by
  have hc : ((146531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16003090103/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((146531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c132 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((480639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log ((132 : ℕ)) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((132 : ℕ)) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -697981/10000000) (δ := 949/125000000) (ψ := 1641/200000) 301 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t132 : ((52290082279/625000000000 : ℚ) : ℝ) ≤ stT301o2 132 := by
  have hc : ((240307/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52290082279/625000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((240307/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c133 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((163741/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log ((133 : ℕ)) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((133 : ℕ)) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2141653/10000000) (δ := 949/125000000) (ψ := 1641/200000) 301 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t133 : ((283940911813/5000000000000 : ℚ) : ℝ) ≤ stT301o2 133 := by
  have hc : ((327457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((283940911813/5000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((327457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c134 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-401549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log ((134 : ℕ)) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((134 : ℕ)) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 496001/1000000) (δ := 3773/250000000) (ψ := 1641/200000) 301 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t134 : ((-346928926531/10000000000000 : ℚ) : ℝ) ≤ stT301o2 134 := by
  have hc : ((-401599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-346928926531/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-401599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c135 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-499627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log ((135 : ℕ)) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((135 : ℕ)) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 775741/1000000) (δ := 949/125000000) (ψ := 1641/200000) 301 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t135 : ((-107507997319/1250000000000 : ℚ) : ℝ) ≤ stT301o2 135 := by
  have hc : ((-124913/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107507997319/1250000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-124913/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c136 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-239151/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log ((136 : ℕ)) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((136 : ℕ)) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5173791/10000000) (δ := 1901/250000000) (ψ := 1641/200000) 301 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t136 : ((-25636468221/625000000000 : ℚ) : ℝ) ≤ stT301o2 136 := by
  have hc : ((-29897/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25636468221/625000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-29897/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c137 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((283911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log ((137 : ℕ)) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((137 : ℕ)) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1208673/5000000) (δ := 3827/500000000) (ψ := 1641/200000) 301 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t137 : ((121269995651/2500000000000 : ℚ) : ℝ) ≤ stT301o2 137 := by
  have hc : ((141943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121269995651/2500000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((141943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c138 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((99187/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log ((138 : ℕ)) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((138 : ℕ)) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 9969/312500) (δ := 7649/1000000000) (ψ := 1641/200000) 301 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t138 : ((5276829537/62500000000 : ℚ) : ℝ) ≤ stT301o2 138 := by
  have hc : ((49591/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5276829537/62500000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((49591/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c139 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((43629/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log ((139 : ℕ)) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((139 : ℕ)) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1517823/5000000) (δ := 7699/1000000000) (ψ := 1641/200000) 301 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t139 : ((37000293077/1250000000000 : ℚ) : ℝ) ≤ stT301o2 139 := by
  have hc : ((174491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37000293077/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((174491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c140 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-82641/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log ((140 : ℕ)) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((140 : ℕ)) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2866397/5000000) (δ := 7649/1000000000) (ψ := 1641/200000) 301 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t140 : ((-55879789259/1000000000000 : ℚ) : ℝ) ≤ stT301o2 140 := by
  have hc : ((-330589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55879789259/1000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-330589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c141 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-487653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log ((141 : ℕ)) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((141 : ℕ)) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -228039/312500) (δ := 7597/1000000000) (ψ := 1641/200000) 301 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t141 : ((-25668687691/312500000000 : ℚ) : ℝ) ≤ stT301o2 141 := by
  have hc : ((-243839/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25668687691/312500000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-243839/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c142 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-280667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log ((142 : ℕ)) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((142 : ℕ)) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2319107/5000000) (δ := 7597/1000000000) (ψ := 1641/200000) 301 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t142 : ((-117786326747/5000000000000 : ℚ) : ℝ) ≤ stT301o2 142 := by
  have hc : ((-280717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117786326747/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-280717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c143 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((348663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log ((143 : ℕ)) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((143 : ℕ)) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -998921/5000000) (δ := 7597/1000000000) (ψ := 1641/200000) 301 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t143 : ((72886434599/1250000000000 : ℚ) : ℝ) ≤ stT301o2 143 := by
  have hc : ((174319/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72886434599/1250000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((174319/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c144 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((484501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log ((144 : ℕ)) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((144 : ℕ)) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 312047/5000000) (δ := 1889/250000000) (ψ := 1641/200000) 301 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t144 : ((100932459627/1250000000000 : ℚ) : ℝ) ≤ stT301o2 144 := by
  have hc : ((121119/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100932459627/1250000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((121119/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c145 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((137997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log ((145 : ℕ)) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((145 : ℕ)) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 806983/2500000) (δ := 7547/1000000000) (ψ := 1641/200000) 301 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t145 : ((14322424911/625000000000 : ℚ) : ℝ) ≤ stT301o2 145 := by
  have hc : ((34493/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14322424911/625000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((34493/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c146 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-137021/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log ((146 : ℕ)) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((146 : ℕ)) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5813861/10000000) (δ := 957/125000000) (ψ := 1641/200000) 301 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t146 : ((-56703838893/1000000000000 : ℚ) : ℝ) ≤ stT301o2 146 := by
  have hc : ((-137031/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56703838893/1000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-137031/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c147 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-97777/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log ((147 : ℕ)) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((147 : ℕ)) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3662929/5000000) (δ := 191/25000000) (ψ := 1641/200000) 301 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t147 : ((-40324661217/500000000000 : ℚ) : ℝ) ≤ stT301o2 147 := by
  have hc : ((-48891/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40324661217/500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-48891/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c148 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-66547/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log ((148 : ℕ)) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((148 : ℕ)) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1193749/2500000) (δ := 769/100000000) (ψ := 1641/200000) 301 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t148 : ((-10941904243/400000000000 : ℚ) : ℝ) ≤ stT301o2 148 := by
  have hc : ((-66557/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10941904243/400000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-66557/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c149 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((124867/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log ((149 : ℕ)) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((149 : ℕ)) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -224129/1000000) (δ := 7713/1000000000) (ψ := 1641/200000) 301 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t149 : ((102286724967/2000000000000 : ℚ) : ℝ) ≤ stT301o2 149 := by
  have hc : ((124857/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102286724967/2000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((124857/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c150 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((496969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log ((150 : ℕ)) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((150 : ℕ)) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 17213/625000) (δ := 759/100000000) (ψ := 1641/200000) 301 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t150 : ((1584971829/19531250000 : ℚ) : ℝ) ≤ stT301o2 150 := by
  have hc : ((31059/31250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1584971829/19531250000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((31059/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c151 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((55563/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log ((151 : ℕ)) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((151 : ℕ)) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2775439/10000000) (δ := 7563/1000000000) (ψ := 1641/200000) 301 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t151 : ((45211416469/1250000000000 : ℚ) : ℝ) ≤ stT301o2 151 := by
  have hc : ((222227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45211416469/1250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((222227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c152 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-253967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log ((152 : ℕ)) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((152 : ℕ)) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 657369/1250000) (δ := 191/25000000) (ψ := 1641/200000) 301 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t152 : ((-6437966973/156250000000 : ℚ) : ℝ) ≤ stT301o2 152 := by
  have hc : ((-31749/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6437966973/156250000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-31749/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c153 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-499347/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log ((153 : ℕ)) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((153 : ℕ)) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3863087/5000000) (δ := 377/50000000) (ψ := 1641/200000) 301 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t153 : ((-100929697879/1250000000000 : ℚ) : ℝ) ≤ stT301o2 153 := by
  have hc : ((-124843/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100929697879/1250000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-124843/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c154 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-598363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log ((154 : ℕ)) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((154 : ℕ)) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5530633/10000000) (δ := 767/100000000) (ψ := 1641/200000) 301 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t154 : ((-482214958899/10000000000000 : ℚ) : ℝ) ≤ stT301o2 154 := by
  have hc : ((-598413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-482214958899/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-598413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c155 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((326553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log ((155 : ℕ)) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((155 : ℕ)) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -619071/2000000) (δ := 381/50000000) (ψ := 1641/200000) 301 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t155 : ((262253413157/10000000000000 : ℚ) : ℝ) ≤ stT301o2 155 := by
  have hc : ((326503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((262253413157/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((326503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c156 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((963693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log ((156 : ℕ)) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((156 : ℕ)) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -675729/10000000) (δ := 757/100000000) (ψ := 1641/200000) 301 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t156 : ((1205517393/15625000000 : ℚ) : ℝ) ≤ stT301o2 156 := by
  have hc : ((963643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1205517393/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((963643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c157 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((770371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log ((157 : ℕ)) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((157 : ℕ)) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1728433/10000000) (δ := 7583/1000000000) (ψ := 1641/200000) 301 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t157 : ((307391202803/5000000000000 : ℚ) : ℝ) ≤ stT301o2 157 := by
  have hc : ((770321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((307391202803/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((770321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c158 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-38029/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log ((158 : ℕ)) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((158 : ℕ)) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 102933/250000) (δ := 767/100000000) (ψ := 1641/200000) 301 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t158 : ((-7568541033/1250000000000 : ℚ) : ℝ) ≤ stT301o2 158 := by
  have hc : ((-19027/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7568541033/1250000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-19027/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c159 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-42753/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log ((159 : ℕ)) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((159 : ℕ)) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1622789/2500000) (δ := 7583/1000000000) (ψ := 1641/200000) 301 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t159 : ((-16953667393/250000000000 : ℚ) : ℝ) ≤ stT301o2 159 := by
  have hc : ((-85511/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16953667393/250000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-85511/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c160 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-460833/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log ((160 : ℕ)) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((160 : ℕ)) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -685787/1000000) (δ := 7577/1000000000) (ψ := 1641/200000) 301 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t160 : ((-18217025453/250000000000 : ℚ) : ℝ) ≤ stT301o2 160 := by
  have hc : ((-230429/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18217025453/250000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-230429/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c161 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-116257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log ((161 : ℕ)) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((161 : ℕ)) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -902729/2000000) (δ := 3863/500000000) (ψ := 1641/200000) 301 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t161 : ((-45821561651/2500000000000 : ℚ) : ℝ) ≤ stT301o2 161 := by
  have hc : ((-58141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45821561651/2500000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-58141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c162 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((6421/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log ((162 : ℕ)) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((162 : ℕ)) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -436781/2000000) (δ := 3863/500000000) (ψ := 1641/200000) 301 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t162 : ((5044419917/100000000000 : ℚ) : ℝ) ≤ stT301o2 162 := by
  have hc : ((12841/20000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5044419917/100000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((12841/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c163 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((998617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log ((163 : ℕ)) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((163 : ℕ)) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 263/20000) (δ := 1919/250000000) (ψ := 1641/200000) 301 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t163 : ((39106879421/500000000000 : ℚ) : ℝ) ≤ stT301o2 163 := by
  have hc : ((998567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39106879421/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((998567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c164 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((562749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log ((164 : ℕ)) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((164 : ℕ)) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2432721/10000000) (δ := 7677/1000000000) (ψ := 1641/200000) 301 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t164 : ((109848410683/2500000000000 : ℚ) : ℝ) ≤ stT301o2 164 := by
  have hc : ((562699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109848410683/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((562699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c165 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-31189/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log ((165 : ℕ)) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((165 : ℕ)) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 589993/1250000) (δ := 1919/250000000) (ψ := 1641/200000) 301 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t165 : ((-12142248903/500000000000 : ℚ) : ℝ) ≤ stT301o2 165 := by
  have hc : ((-15597/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12142248903/500000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-15597/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c166 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-941329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log ((166 : ℕ)) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((166 : ℕ)) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 87417/125000) (δ := 7627/1000000000) (ψ := 1641/200000) 301 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t166 : ((-730652252229/10000000000000 : ℚ) : ℝ) ≤ stT301o2 166 := by
  have hc : ((-941379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-730652252229/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-941379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c167 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-847431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log ((167 : ℕ)) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((167 : ℕ)) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -806851/1250000) (δ := 1537/200000000) (ψ := 1641/200000) 301 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t167 : ((-10246892771/156250000000 : ℚ) : ℝ) ≤ stT301o2 167 := by
  have hc : ((-847481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10246892771/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-847481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c168 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-112389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log ((168 : ℕ)) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((168 : ℕ)) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2104279/5000000) (δ := 1527/200000000) (ψ := 1641/200000) 301 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t168 : ((-86748599963/10000000000000 : ℚ) : ℝ) ≤ stT301o2 168 := by
  have hc : ((-112439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86748599963/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-112439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c169 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((351839/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log ((169 : ℕ)) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((169 : ℕ)) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -197559/1000000) (δ := 3809/500000000) (ψ := 1641/200000) 301 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t169 : ((13531294161/250000000000 : ℚ) : ℝ) ≤ stT301o2 169 := by
  have hc : ((175907/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13531294161/250000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((175907/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c170 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((497617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log ((170 : ℕ)) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((170 : ℕ)) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 61043/2500000) (δ := 1917/250000000) (ψ := 1641/200000) 301 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t170 : ((11926098459/156250000000 : ℚ) : ℝ) ≤ stT301o2 170 := by
  have hc : ((62199/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11926098459/156250000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((62199/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c171 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((278359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log ((171 : ℕ)) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((171 : ℕ)) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 612729/2500000) (δ := 3809/500000000) (ψ := 1641/200000) 301 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t171 : ((106423649073/2500000000000 : ℚ) : ℝ) ≤ stT301o2 171 := by
  have hc : ((139167/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106423649073/2500000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((139167/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c172 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-35399/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log ((172 : ℕ)) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((172 : ℕ)) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 580599/1250000) (δ := 1917/250000000) (ψ := 1641/200000) 301 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t172 : ((-107985021153/5000000000000 : ℚ) : ℝ) ≤ stT301o2 172 := by
  have hc : ((-141621/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107985021153/5000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-141621/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c173 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-916637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log ((173 : ℕ)) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((173 : ℕ)) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6825951/10000000) (δ := 3809/500000000) (ψ := 1641/200000) 301 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t173 : ((-348472146241/5000000000000 : ℚ) : ℝ) ≤ stT301o2 173 := by
  have hc : ((-916687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-348472146241/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-916687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c174 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-448861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log ((174 : ℕ)) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((174 : ℕ)) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -335671/500000) (δ := 7561/1000000000) (ψ := 1641/200000) 301 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t174 : ((-170150013857/2500000000000 : ℚ) : ℝ) ≤ stT301o2 174 := by
  have hc : ((-224443/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170150013857/2500000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-224443/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c175 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-249439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log ((175 : ℕ)) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((175 : ℕ)) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1139311/2500000) (δ := 3771/500000000) (ψ := 1641/200000) 301 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t175 : ((-188595970281/10000000000000 : ℚ) : ℝ) ≤ stT301o2 175 := by
  have hc : ((-249489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188595970281/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-249489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c176 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((56913/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log ((176 : ℕ)) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((176 : ℕ)) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -603343/2500000) (δ := 7711/1000000000) (ψ := 1641/200000) 301 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t176 : ((5361999803/125000000000 : ℚ) : ℝ) ≤ stT301o2 176 := by
  have hc : ((14227/25000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5361999803/125000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((14227/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c177 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((496831/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log ((177 : ℕ)) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((177 : ℕ)) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -140807/5000000) (δ := 3821/500000000) (ψ := 1641/200000) 301 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t177 : ((93355560669/1250000000000 : ℚ) : ℝ) ≤ stT301o2 177 := by
  have hc : ((248403/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93355560669/1250000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((248403/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c178 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((741669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log ((178 : ℕ)) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((178 : ℕ)) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1838103/10000000) (δ := 3771/500000000) (ψ := 1641/200000) 301 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t178 : ((555866430689/10000000000000 : ℚ) : ℝ) ≤ stT301o2 178 := by
  have hc : ((741619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((555866430689/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((741619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c179 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-7591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log ((179 : ℕ)) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((179 : ℕ)) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 246623/625000) (δ := 7661/1000000000) (ψ := 1641/200000) 301 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t179 : ((-1427789619/2500000000000 : ℚ) : ℝ) ≤ stT301o2 179 := by
  have hc : ((-7641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1427789619/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-7641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c180 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-187163/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log ((180 : ℕ)) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((180 : ℕ)) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6042057/10000000) (δ := 7561/1000000000) (ψ := 1641/200000) 301 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t180 : ((-69756190989/1250000000000 : ℚ) : ℝ) ≤ stT301o2 180 := by
  have hc : ((-374351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69756190989/1250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-374351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c181 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-497031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log ((181 : ℕ)) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((181 : ℕ)) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3790703/5000000) (δ := 3777/500000000) (ψ := 1641/200000) 301 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t181 : ((-2309120247/31250000000 : ℚ) : ℝ) ≤ stT301o2 181 := by
  have hc : ((-15533/15625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2309120247/31250000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-15533/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c182 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-29561/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log ((182 : ℕ)) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((182 : ℕ)) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5508419/10000000) (δ := 3777/500000000) (ψ := 1641/200000) 301 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t182 : ((-35062311/800000000 : ℚ) : ℝ) ≤ stT301o2 182 := by
  have hc : ((-59127/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35062311/800000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-59127/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c183 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((95457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log ((183 : ℕ)) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((183 : ℕ)) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3446757/10000000) (δ := 7549/1000000000) (ψ := 1641/200000) 301 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t183 : ((8818167309/625000000000 : ℚ) : ℝ) ≤ stT301o2 183 := by
  have hc : ((11929/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8818167309/625000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((11929/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c184 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((848031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log ((184 : ℕ)) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((184 : ℕ)) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -279269/2000000) (δ := 7549/1000000000) (ψ := 1641/200000) 301 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t184 : ((625139225029/10000000000000 : ℚ) : ℝ) ≤ stT301o2 184 := by
  have hc : ((847981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((625139225029/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((847981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c185 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((967109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log ((185 : ℕ)) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((185 : ℕ)) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 80371/1250000) (δ := 7699/1000000000) (ψ := 1641/200000) 301 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t185 : ((355497657813/5000000000000 : ℚ) : ℝ) ≤ stT301o2 185 := by
  have hc : ((967059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((355497657813/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((967059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c186 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((481437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log ((186 : ℕ)) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((186 : ℕ)) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 333907/1250000) (δ := 3777/500000000) (ψ := 1641/200000) 301 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t186 : ((70593959389/2000000000000 : ℚ) : ℝ) ≤ stT301o2 186 := by
  have hc : ((481387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70593959389/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((481387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c187 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-59999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log ((187 : ℕ)) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((187 : ℕ)) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4688709/10000000) (δ := 7699/1000000000) (ψ := 1641/200000) 301 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t187 : ((-43882961457/2000000000000 : ℚ) : ℝ) ≤ stT301o2 187 := by
  have hc : ((-60009/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43882961457/2000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-60009/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c188 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-894517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log ((188 : ℕ)) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((188 : ℕ)) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6695363/10000000) (δ := 7649/1000000000) (ψ := 1641/200000) 301 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t188 : ((-26097203091/400000000000 : ℚ) : ℝ) ≤ stT301o2 188 := by
  have hc : ((-894567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26097203091/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-894567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c189 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-47221/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log ((189 : ℕ)) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((189 : ℕ)) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7016557/10000000) (δ := 7647/1000000000) (ψ := 1641/200000) 301 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t189 : ((-68700086671/1000000000000 : ℚ) : ℝ) ≤ stT301o2 189 := by
  have hc : ((-94447/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68700086671/1000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-94447/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c190 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-427421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log ((190 : ℕ)) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((190 : ℕ)) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1006217/2000000) (δ := 3853/500000000) (ψ := 1641/200000) 301 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t190 : ((-310120378667/10000000000000 : ℚ) : ℝ) ≤ stT301o2 190 := by
  have hc : ((-427471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310120378667/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-427471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c191 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((341391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log ((191 : ℕ)) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((191 : ℕ)) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3055999/10000000) (δ := 7647/1000000000) (ψ := 1641/200000) 301 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t191 : ((123492736367/5000000000000 : ℚ) : ℝ) ≤ stT301o2 191 := by
  have hc : ((341341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123492736367/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((341341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c192 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((181247/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log ((192 : ℕ)) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((192 : ℕ)) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1091259/10000000) (δ := 7597/1000000000) (ψ := 1641/200000) 301 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t192 : ((130796386819/2000000000000 : ℚ) : ℝ) ≤ stT301o2 192 := by
  have hc : ((181237/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130796386819/2000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((181237/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c193 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((940969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log ((193 : ℕ)) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((193 : ℕ)) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 172657/2000000) (δ := 957/125000000) (ψ := 1641/200000) 301 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t193 : ((135457521997/2000000000000 : ℚ) : ℝ) ≤ stT301o2 193 := by
  have hc : ((940919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135457521997/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((940919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c194 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((108223/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log ((194 : ℕ)) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((194 : ℕ)) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 561549/2000000) (δ := 957/125000000) (ψ := 1641/200000) 301 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t194 : ((77690594159/2500000000000 : ℚ) : ℝ) ≤ stT301o2 194 := by
  have hc : ((216421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77690594159/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((216421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c195 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-160167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log ((195 : ℕ)) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((195 : ℕ)) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1185549/2500000) (δ := 7697/1000000000) (ψ := 1641/200000) 301 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t195 : ((-358487169/15625000000 : ℚ) : ℝ) ≤ stT301o2 195 := by
  have hc : ((-5006/15625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-358487169/15625000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-5006/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c196 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-444671/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log ((196 : ℕ)) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((196 : ℕ)) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6666753/10000000) (δ := 3803/500000000) (ψ := 1641/200000) 301 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t196 : ((-19852507941/312500000000 : ℚ) : ℝ) ≤ stT301o2 196 := by
  have hc : ((-55587/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19852507941/312500000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-55587/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c197 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-14968/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log ((197 : ℕ)) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((197 : ℕ)) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7126437/10000000) (δ := 769/100000000) (ψ := 1641/200000) 301 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t197 : ((-341274321471/5000000000000 : ℚ) : ℝ) ≤ stT301o2 197 := by
  have hc : ((-479001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-341274321471/5000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-479001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c198 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-30933/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log ((198 : ℕ)) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((198 : ℕ)) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -522137/1000000) (δ := 377/50000000) (ψ := 1641/200000) 301 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t198 : ((-17588300763/500000000000 : ℚ) : ℝ) ≤ stT301o2 198 := by
  have hc : ((-247489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17588300763/500000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-247489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c199 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((238127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log ((199 : ℕ)) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((199 : ℕ)) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1662949/5000000) (δ := 191/25000000) (ψ := 1641/200000) 301 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t199 : ((168768261837/10000000000000 : ℚ) : ℝ) ≤ stT301o2 199 := by
  have hc : ((238077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168768261837/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((238077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c200 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((41933/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log ((200 : ℕ)) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((200 : ℕ)) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -287989/2000000) (δ := 769/100000000) (ψ := 1641/200000) 301 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t200 : ((29649308133/500000000000 : ℚ) : ℝ) ≤ stT301o2 200 := by
  have hc : ((83861/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29649308133/500000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((83861/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c201 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((492393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log ((201 : ℕ)) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((201 : ℕ)) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2729/62500) (δ := 7563/1000000000) (ψ := 1641/200000) 301 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t201 : ((4341116337/62500000000 : ℚ) : ℝ) ≤ stT301o2 201 := by
  have hc : ((30773/31250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4341116337/62500000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((30773/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c202 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((37787/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log ((202 : ℕ)) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((202 : ℕ)) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 143991/625000) (δ := 7613/1000000000) (ψ := 1641/200000) 301 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t202 : ((212676968787/5000000000000 : ℚ) : ℝ) ≤ stT301o2 202 := by
  have hc : ((302271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212676968787/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((302271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c203 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-46911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log ((203 : ℕ)) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((203 : ℕ)) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4161891/10000000) (δ := 759/100000000) (ψ := 1641/200000) 301 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t203 : ((-4117830221/625000000000 : ℚ) : ℝ) ≤ stT301o2 203 := by
  have hc : ((-5867/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4117830221/625000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-5867/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c204 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-740301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log ((204 : ℕ)) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((204 : ℕ)) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 187837/312500) (δ := 7663/1000000000) (ψ := 1641/200000) 301 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t204 : ((-518350089491/10000000000000 : ℚ) : ℝ) ≤ stT301o2 204 := by
  have hc : ((-740351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-518350089491/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-740351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c205 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log ((205 : ℕ)) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((205 : ℕ)) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3925323/5000000) (δ := 759/100000000) (ψ := 1641/200000) 301 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t205 : ((-698465223119/10000000000000 : ℚ) : ℝ) ≤ stT301o2 205 := by
  have hc : ((-1000049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-698465223119/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-1000049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c206 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-93061/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log ((206 : ℕ)) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((206 : ℕ)) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6026409/10000000) (δ := 767/100000000) (ψ := 1641/200000) 301 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t206 : ((-129686234723/2500000000000 : ℚ) : ℝ) ≤ stT301o2 206 := by
  have hc : ((-372269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129686234723/2500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-372269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c207 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-110729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log ((207 : ℕ)) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((207 : ℕ)) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4204381/10000000) (δ := 757/100000000) (ψ := 1641/200000) 301 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t207 : ((-76996833171/10000000000000 : ℚ) : ℝ) ≤ stT301o2 207 := by
  have hc : ((-110779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76996833171/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-110779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c208 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((288213/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log ((208 : ℕ)) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((208 : ℕ)) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2391119/10000000) (δ := 193/25000000) (ψ := 1641/200000) 301 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t208 : ((399644709/10000000000 : ℚ) : ℝ) ≤ stT301o2 208 := by
  have hc : ((72047/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399644709/10000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((72047/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c209 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((972603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log ((209 : ℕ)) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((209 : ℕ)) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -586549/10000000) (δ := 381/50000000) (ψ := 1641/200000) 301 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t209 : ((336364262921/5000000000000 : ℚ) : ℝ) ≤ stT301o2 209 := by
  have hc : ((972553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336364262921/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((972553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c210 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((885251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log ((210 : ℕ)) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((210 : ℕ)) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 241881/2000000) (δ := 757/100000000) (ψ := 1641/200000) 301 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t210 : ((122169245613/2000000000000 : ℚ) : ℝ) ≤ stT301o2 210 := by
  have hc : ((885201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122169245613/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((885201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c211 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((45443/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log ((211 : ℕ)) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((211 : ℕ)) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1498409/5000000) (δ := 7583/1000000000) (ψ := 1641/200000) 301 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t211 : ((31279930929/1250000000000 : ℚ) : ℝ) ≤ stT301o2 211 := by
  have hc : ((181747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31279930929/1250000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((181747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c212 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-13321/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log ((212 : ℕ)) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((212 : ℕ)) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2387883/5000000) (δ := 381/50000000) (ψ := 1641/200000) 301 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t212 : ((-9150276369/400000000000 : ℚ) : ℝ) ≤ stT301o2 212 := by
  have hc : ((-13323/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9150276369/400000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-13323/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c213 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-866301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log ((213 : ℕ)) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((213 : ℕ)) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6546361/10000000) (δ := 767/100000000) (ψ := 1641/200000) 301 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t213 : ((-593614175339/10000000000000 : ℚ) : ℝ) ≤ stT301o2 213 := by
  have hc : ((-866351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-593614175339/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-866351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c214 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-491753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log ((214 : ℕ)) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((214 : ℕ)) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1479857/2000000) (δ := 1907/250000000) (ψ := 1641/200000) 301 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t214 : ((-84043138977/1250000000000 : ℚ) : ℝ) ≤ stT301o2 214 := by
  have hc : ((-245889/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84043138977/1250000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-245889/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c215 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-317221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log ((215 : ℕ)) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((215 : ℕ)) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -705651/1250000) (δ := 61/8000000) (ψ := 1641/200000) 301 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t215 : ((-21636018577/500000000000 : ℚ) : ℝ) ≤ stT301o2 215 := by
  have hc : ((-158623/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21636018577/500000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-158623/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c216 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((11093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log ((216 : ℕ)) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((216 : ℕ)) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3899257/10000000) (δ := 1907/250000000) (ψ := 1641/200000) 301 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t216 : ((7513800759/10000000000000 : ℚ) : ℝ) ≤ stT301o2 216 := by
  have hc : ((11043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7513800759/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((11043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c217 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((40561/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log ((217 : ℕ)) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((217 : ℕ)) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -540349/2500000) (δ := 3789/500000000) (ψ := 1641/200000) 301 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t217 : ((55064940193/1250000000000 : ℚ) : ℝ) ≤ stT301o2 217 := by
  have hc : ((324463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55064940193/1250000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((324463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c218 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((985141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log ((218 : ℕ)) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((218 : ℕ)) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -53939/1250000) (δ := 309/40000000) (ψ := 1641/200000) 301 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t218 : ((133437471587/2000000000000 : ℚ) : ℝ) ≤ stT301o2 218 := by
  have hc : ((985091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133437471587/2000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((985091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c219 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((869707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log ((219 : ℕ)) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((219 : ℕ)) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 161309/1250000) (δ := 3789/500000000) (ψ := 1641/200000) 301 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t219 : ((587659412209/10000000000000 : ℚ) : ℝ) ≤ stT301o2 219 := by
  have hc : ((869657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((587659412209/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((869657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c220 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((72129/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log ((220 : ℕ)) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((220 : ℕ)) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 187787/625000) (δ := 3839/500000000) (ψ := 1641/200000) 301 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t220 : ((48622557681/2000000000000 : ℚ) : ℝ) ≤ stT301o2 220 := by
  have hc : ((72119/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48622557681/2000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((72119/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c221 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-154237/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log ((221 : ℕ)) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((221 : ℕ)) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4710961/10000000) (δ := 3839/500000000) (ψ := 1641/200000) 301 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t221 : ((-51883941163/2500000000000 : ℚ) : ℝ) ≤ stT301o2 221 := by
  have hc : ((-77131/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51883941163/2500000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-77131/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c222 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-104711/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log ((222 : ℕ)) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((222 : ℕ)) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6409579/10000000) (δ := 3789/500000000) (ψ := 1641/200000) 301 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t222 : ((-281126861433/5000000000000 : ℚ) : ℝ) ≤ stT301o2 222 := by
  have hc : ((-418869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-281126861433/5000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-418869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c223 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-497569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log ((223 : ℕ)) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((223 : ℕ)) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3803683/5000000) (δ := 1537/200000000) (ψ := 1641/200000) 301 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t223 : ((-3332138221/50000000000 : ℚ) : ℝ) ≤ stT301o2 223 := by
  have hc : ((-248797/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3332138221/50000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-248797/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c224 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-716497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log ((224 : ℕ)) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((224 : ℕ)) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5923911/10000000) (δ := 1507/200000000) (ψ := 1641/200000) 301 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t224 : ((-239381872119/5000000000000 : ℚ) : ℝ) ≤ stT301o2 224 := by
  have hc : ((-716547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239381872119/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-716547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c225 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-128029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log ((225 : ℕ)) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((225 : ℕ)) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4247943/10000000) (δ := 1507/200000000) (ψ := 1641/200000) 301 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t225 : ((-85386042693/10000000000000 : ℚ) : ℝ) ≤ stT301o2 225 := by
  have hc : ((-128079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85386042693/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-128079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c226 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((256647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log ((226 : ℕ)) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((226 : ℕ)) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -644861/2500000) (δ := 7609/500000000) (ψ := 1641/200000) 301 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t226 : ((8535119409/250000000000 : ℚ) : ℝ) ≤ stT301o2 226 := by
  have hc : ((128311/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8535119409/250000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((128311/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c227 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((58331/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log ((227 : ℕ)) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((227 : ℕ)) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -918281/10000000) (δ := 1507/200000000) (ψ := 1641/200000) 301 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t227 : ((309708417429/5000000000000 : ℚ) : ℝ) ≤ stT301o2 227 := by
  have hc : ((466623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((309708417429/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((466623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c228 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((957027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log ((228 : ℕ)) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((228 : ℕ)) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 735563/10000000) (δ := 3859/500000000) (ψ := 1641/200000) 301 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t228 : ((316886664941/5000000000000 : ℚ) : ℝ) ≤ stT301o2 228 := by
  have hc : ((956977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316886664941/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((956977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c229 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((579343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log ((229 : ℕ)) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((229 : ℕ)) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 297773/1250000) (δ := 1507/200000000) (ψ := 1641/200000) 301 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t229 : ((191403620837/5000000000000 : ℚ) : ℝ) ≤ stT301o2 229 := by
  have hc : ((579293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191403620837/5000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((579293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c230 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-18921/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log ((230 : ℕ)) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((230 : ℕ)) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2010809/5000000) (δ := 473/62500000) (ψ := 1641/200000) 301 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t230 : ((-6246316213/2500000000000 : ℚ) : ℝ) ≤ stT301o2 230 := by
  have hc : ((-9473/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6246316213/2500000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-9473/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c231 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-637139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log ((231 : ℕ)) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((231 : ℕ)) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5653941/10000000) (δ := 473/62500000) (ψ := 1641/200000) 301 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t231 : ((-13101243029/312500000000 : ℚ) : ℝ) ≤ stT301o2 231 := by
  have hc : ((-637189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13101243029/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-637189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c232 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-194737/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log ((232 : ℕ)) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((232 : ℕ)) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7279191/10000000) (δ := 1537/200000000) (ψ := 1641/200000) 301 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t232 : ((-127857832151/2000000000000 : ℚ) : ℝ) ≤ stT301o2 232 := by
  have hc : ((-194747/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127857832151/2000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-194747/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c233 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-457073/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log ((233 : ℕ)) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((233 : ℕ)) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1702621/2500000) (δ := 7611/1000000000) (ψ := 1641/200000) 301 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t233 : ((-74863738989/1250000000000 : ℚ) : ℝ) ≤ stT301o2 233 := by
  have hc : ((-228549/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74863738989/1250000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-228549/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c234 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-243587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log ((234 : ℕ)) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((234 : ℕ)) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2599559/5000000) (δ := 7561/1000000000) (ψ := 1641/200000) 301 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t234 : ((-39813570063/1250000000000 : ℚ) : ℝ) ≤ stT301o2 234 := by
  have hc : ((-60903/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39813570063/1250000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-60903/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c235 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((2651/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log ((235 : ℕ)) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((235 : ℕ)) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3594637/10000000) (δ := 1923/250000000) (ψ := 1641/200000) 301 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t235 : ((4321673/500000000 : ℚ) : ℝ) ≤ stT301o2 235 := by
  have hc : ((53/400 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4321673/500000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((53/400 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c236 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((87197/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log ((236 : ℕ)) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((236 : ℕ)) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1996967/10000000) (δ := 3771/500000000) (ψ := 1641/200000) 301 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t236 : ((3547268473/78125000000 : ℚ) : ℝ) ≤ stT301o2 236 := by
  have hc : ((348763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3547268473/78125000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((348763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c237 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((493419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log ((237 : ℕ)) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((237 : ℕ)) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -406069/10000000) (δ := 949/125000000) (ψ := 1641/200000) 301 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t237 : ((160246723593/2500000000000 : ℚ) : ℝ) ≤ stT301o2 237 := by
  have hc : ((246697/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160246723593/2500000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((246697/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c238 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((891/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log ((238 : ℕ)) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((238 : ℕ)) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1178131/10000000) (δ := 7711/1000000000) (ψ := 1641/200000) 301 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t238 : ((11550329257/200000000000 : ℚ) : ℝ) ≤ stT301o2 238 := by
  have hc : ((17819/20000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11550329257/200000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((17819/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c239 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((451559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log ((239 : ℕ)) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((239 : ℕ)) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 275571/1000000) (δ := 7561/1000000000) (ψ := 1641/200000) 301 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t239 : ((146028395307/5000000000000 : ℚ) : ℝ) ≤ stT301o2 239 := by
  have hc : ((451509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146028395307/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((451509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c240 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-31841/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log ((240 : ℕ)) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((240 : ℕ)) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 270419/625000) (δ := 7661/1000000000) (ψ := 1641/200000) 301 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t240 : ((-10279878399/1000000000000 : ℚ) : ℝ) ≤ stT301o2 240 := by
  have hc : ((-31851/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10279878399/1000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-31851/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c241 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-141459/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log ((241 : ℕ)) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((241 : ℕ)) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 368197/625000) (δ := 949/125000000) (ψ := 1641/200000) 301 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t241 : ((-91128246633/2000000000000 : ℚ) : ℝ) ≤ stT301o2 241 := by
  have hc : ((-141469/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91128246633/2000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-141469/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c242 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-246729/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log ((242 : ℕ)) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((242 : ℕ)) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 931141/1250000) (δ := 949/125000000) (ψ := 1641/200000) 301 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t242 : ((-12688928379/200000000000 : ℚ) : ℝ) ≤ stT301o2 242 := by
  have hc : ((-493483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12688928379/200000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-493483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c243 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-2802/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log ((243 : ℕ)) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((243 : ℕ)) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6707293/10000000) (δ := 7649/1000000000) (ψ := 1641/200000) 301 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t243 : ((-57522753169/1000000000000 : ℚ) : ℝ) ≤ stT301o2 243 := by
  have hc : ((-89669/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57522753169/1000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-89669/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c244 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-474193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log ((244 : ℕ)) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((244 : ℕ)) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -516211/1000000) (δ := 1901/250000000) (ψ := 1641/200000) 301 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t244 : ((-60720650991/2000000000000 : ℚ) : ℝ) ≤ stT301o2 244 := by
  have hc : ((-474243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60720650991/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-474243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c245 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((121191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log ((245 : ℕ)) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((245 : ℕ)) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1811633/5000000) (δ := 15099/1000000000) (ψ := 1641/200000) 301 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t245 : ((19348519379/2500000000000 : ℚ) : ℝ) ≤ stT301o2 245 := by
  have hc : ((121141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19348519379/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((121141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c246 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((335119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log ((246 : ℕ)) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((246 : ℕ)) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -522667/2500000) (δ := 7599/1000000000) (ψ := 1641/200000) 301 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t246 : ((13352993259/312500000000 : ℚ) : ℝ) ≤ stT301o2 246 := by
  have hc : ((167547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13352993259/312500000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((167547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c247 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((974633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log ((247 : ℕ)) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((247 : ℕ)) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -564297/10000000) (δ := 7599/1000000000) (ψ := 1641/200000) 301 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t247 : ((155027892393/2500000000000 : ℚ) : ℝ) ≤ stT301o2 247 := by
  have hc : ((974583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155027892393/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((974583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c248 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((463893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log ((248 : ℕ)) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((248 : ℕ)) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 955903/10000000) (δ := 3827/500000000) (ψ := 1641/200000) 301 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t248 : ((14727809/250000000 : ℚ) : ℝ) ≤ stT301o2 248 := by
  have hc : ((115967/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14727809/250000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((115967/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c249 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((55037/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log ((249 : ℕ)) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((249 : ℕ)) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2469971/10000000) (δ := 7549/1000000000) (ψ := 1641/200000) 301 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t249 : ((1089846849/31250000000 : ℚ) : ℝ) ≤ stT301o2 249 := by
  have hc : ((6879/12500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1089846849/31250000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((6879/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c250 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-2041/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log ((250 : ℕ)) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((250 : ℕ)) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3978019/10000000) (δ := 7699/1000000000) (ψ := 1641/200000) 301 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t250 : ((-80875311/62500000000 : ℚ) : ℝ) ≤ stT301o2 250 := by
  have hc : ((-1023/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80875311/62500000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-1023/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c251 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((251 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-582017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55254529/20000000 : ℚ) : ℝ) ≤ Real.log ((251 : ℕ)) / 2 := by
    have h := (log_br_251).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((251 : ℕ)) / 2 ≤ ((5525453/2000000 : ℚ) : ℝ) := by
    have h := (log_br_251).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5480009/10000000) (δ := 7699/1000000000) (ψ := 1641/200000) 301 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t251 : ((-73479556013/2000000000000 : ℚ) : ℝ) ≤ stT301o2 251 := by
  have hc : ((-582067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((251 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73479556013/2000000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-582067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c252 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((252 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-187793/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5529429/2000000 : ℚ) : ℝ) ≤ Real.log ((252 : ℕ)) / 2 := by
    have h := (log_br_252).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((252 : ℕ)) / 2 ≤ ((55294291/20000000 : ℚ) : ℝ) := by
    have h := (log_br_252).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 436001/625000) (δ := 1901/250000000) (ψ := 1641/200000) 301 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t252 : ((-118304809623/2000000000000 : ℚ) : ℝ) ≤ stT301o2 252 := by
  have hc : ((-187803/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((252 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118304809623/2000000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-187803/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c253 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((253 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-970173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27666947/10000000 : ℚ) : ℝ) ≤ Real.log ((253 : ℕ)) / 2 := by
    have h := (log_br_253).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((253 : ℕ)) / 2 ≤ ((11066779/4000000 : ℚ) : ℝ) := by
    have h := (log_br_253).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7241847/10000000) (δ := 7697/1000000000) (ψ := 1641/200000) 301 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t253 : ((-121994869797/2000000000000 : ℚ) : ℝ) ≤ stT301o2 253 := by
  have hc : ((-970223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((253 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121994869797/2000000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-970223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c254 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((254 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-133709/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27686671/10000000 : ℚ) : ℝ) ≤ Real.log ((254 : ℕ)) / 2 := by
    have h := (log_br_254).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((254 : ℕ)) / 2 ≤ ((55373343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_254).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -359851/625000) (δ := 7697/1000000000) (ψ := 1641/200000) 301 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t254 : ((-327745269/7812500000 : ℚ) : ℝ) ≤ stT301o2 254 := by
  have hc : ((-133719/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((254 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-327745269/7812500000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-133719/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c255 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((255 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-17553/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11082527/4000000 : ℚ) : ℝ) ≤ Real.log ((255 : ℕ)) / 2 := by
    have h := (log_br_255).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((255 : ℕ)) / 2 ≤ ((13853159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_255).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -267451/625000) (δ := 3853/500000000) (ψ := 1641/200000) 301 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t255 : ((-1759366613/200000000000 : ℚ) : ℝ) ≤ stT301o2 255 := by
  have hc : ((-70237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((255 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1759366613/200000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-70237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c256 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((256 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((4333/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27725887/10000000 : ℚ) : ℝ) ≤ Real.log ((256 : ℕ)) / 2 := by
    have h := (log_br_256).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((256 : ℕ)) / 2 ≤ ((2218071/800000 : ℚ) : ℝ) := by
    have h := (log_br_256).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -701653/2500000) (δ := 7697/1000000000) (ψ := 1641/200000) 301 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t256 : ((1733/64000 : ℚ) : ℝ) ≤ stT301o2 256 := by
  have hc : ((1733/4000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((256 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1733/64000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((1733/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c257 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((257 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((859807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1387269/500000 : ℚ) : ℝ) ≤ Real.log ((257 : ℕ)) / 2 := by
    have h := (log_br_257).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((257 : ℕ)) / 2 ≤ ((55490761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_257).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1339763/10000000) (δ := 957/125000000) (ψ := 1641/200000) 301 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t257 : ((268150470487/5000000000000 : ℚ) : ℝ) ≤ stT301o2 257 := by
  have hc : ((859757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((257 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268150470487/5000000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((859757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c258 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((258 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((998821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11105919/4000000 : ℚ) : ℝ) ≤ Real.log ((258 : ℕ)) / 2 := by
    have h := (log_br_258).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((258 : ℕ)) / 2 ≤ ((13882399/5000000 : ℚ) : ℝ) := by
    have h := (log_br_258).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 30351/2500000) (δ := 3853/500000000) (ψ := 1641/200000) 301 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t258 : ((155451714753/2500000000000 : ℚ) : ℝ) ≤ stT301o2 258 := by
  have hc : ((998771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((258 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155451714753/2500000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((998771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c259 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((259 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((807573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1389207/500000 : ℚ) : ℝ) ≤ Real.log ((259 : ℕ)) / 2 := by
    have h := (log_br_259).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((259 : ℕ)) / 2 ≤ ((55568281/20000000 : ℚ) : ℝ) := by
    have h := (log_br_259).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1576927/10000000) (δ := 957/125000000) (ψ := 1641/200000) 301 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t259 : ((501769758987/10000000000000 : ℚ) : ℝ) ≤ stT301o2 259 := by
  have hc : ((807523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((259 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((501769758987/10000000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((807523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c260 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((260 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((352329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1737713/625000 : ℚ) : ℝ) ≤ Real.log ((260 : ℕ)) / 2 := by
    have h := (log_br_260).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((260 : ℕ)) / 2 ≤ ((55606817/20000000 : ℚ) : ℝ) := by
    have h := (log_br_260).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 756711/2500000) (δ := 957/125000000) (ψ := 1641/200000) 301 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t260 : ((218473924267/10000000000000 : ℚ) : ℝ) ≤ stT301o2 260 := by
  have hc : ((352279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((260 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).1
  have hw2 : ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((620173/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218473924267/10000000000000 : ℚ) : ℝ)
      = ((620173/10000000 : ℚ) : ℝ) * ((352279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c261 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((261 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-43193/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13911301/5000000 : ℚ) : ℝ) ≤ Real.log ((261 : ℕ)) / 2 := by
    have h := (log_br_261).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((261 : ℕ)) / 2 ≤ ((11129041/4000000 : ℚ) : ℝ) := by
    have h := (log_br_261).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 558899/1250000) (δ := 7597/1000000000) (ψ := 1641/200000) 301 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t261 : ((-5348401791/400000000000 : ℚ) : ℝ) ≤ stT301o2 261 := by
  have hc : ((-43203/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((261 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5348401791/400000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-43203/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c262 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((262 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-712607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13920861/5000000 : ℚ) : ℝ) ≤ Real.log ((262 : ℕ)) / 2 := by
    have h := (log_br_262).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((262 : ℕ)) / 2 ≤ ((55683447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_262).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 591001/1000000) (δ := 177/7812500) (ψ := 1641/200000) 301 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t262 : ((-440281632571/10000000000000 : ℚ) : ℝ) ≤ stT301o2 262 := by
  have hc : ((-712657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((262 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-440281632571/10000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-712657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c263 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((263 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-244803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2786077/1000000 : ℚ) : ℝ) ≤ Real.log ((263 : ℕ)) / 2 := by
    have h := (log_br_263).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((263 : ℕ)) / 2 ≤ ((55721541/20000000 : ℚ) : ℝ) := by
    have h := (log_br_263).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3671667/5000000) (δ := 7597/1000000000) (ψ := 1641/200000) 301 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t263 : ((-301919694637/5000000000000 : ℚ) : ℝ) ≤ stT301o2 263 := by
  have hc : ((-489631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((263 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).2
  have h0 : (0:ℝ) ≤ ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-301919694637/5000000000000 : ℚ) : ℝ)
      = ((616627/10000000 : ℚ) : ℝ) * ((-489631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c264 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((264 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-933443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5575949/2000000 : ℚ) : ℝ) ≤ Real.log ((264 : ℕ)) / 2 := by
    have h := (log_br_264).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((264 : ℕ)) / 2 ≤ ((55759493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_264).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6936723/10000000) (δ := 22689/1000000000) (ψ := 1641/200000) 301 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t264 : ((-287262867397/5000000000000 : ℚ) : ℝ) ≤ stT301o2 264 := by
  have hc : ((-933493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((264 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).2
  have h0 : (0:ℝ) ≤ ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-287262867397/5000000000000 : ℚ) : ℝ)
      = ((307729/5000000 : ℚ) : ℝ) * ((-933493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c265 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((265 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-118619/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27898649/10000000 : ℚ) : ℝ) ≤ Real.log ((265 : ℕ)) / 2 := by
    have h := (log_br_265).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((265 : ℕ)) / 2 ≤ ((55797299/20000000 : ℚ) : ℝ) := by
    have h := (log_br_265).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2757117/5000000) (δ := 479/62500000) (ψ := 1641/200000) 301 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t265 : ((-9109165023/250000000000 : ℚ) : ℝ) ≤ stT301o2 265 := by
  have hc : ((-118629/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((265 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).2
  have h0 : (0:ℝ) ≤ ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9109165023/250000000000 : ℚ) : ℝ)
      = ((76787/1250000 : ℚ) : ℝ) * ((-118629/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c266 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((266 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-67987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55834963/20000000 : ℚ) : ℝ) ≤ Real.log ((266 : ℕ)) / 2 := by
    have h := (log_br_266).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((266 : ℕ)) / 2 ≤ ((13958741/5000000 : ℚ) : ℝ) := by
    have h := (log_br_266).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4097089/10000000) (δ := 7639/1000000000) (ψ := 1641/200000) 301 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t266 : ((-2085810309/500000000000 : ℚ) : ℝ) ≤ stT301o2 266 := by
  have hc : ((-68037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((266 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2085810309/500000000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-68037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c267 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((267 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((476511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27936243/10000000 : ℚ) : ℝ) ≤ Real.log ((267 : ℕ)) / 2 := by
    have h := (log_br_267).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((267 : ℕ)) / 2 ≤ ((55872487/20000000 : ℚ) : ℝ) := by
    have h := (log_br_267).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1342643/5000000) (δ := 7589/1000000000) (ψ := 1641/200000) 301 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t267 : ((29158936739/1000000000000 : ℚ) : ℝ) ≤ stT301o2 267 := by
  have hc : ((476461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((267 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).1
  have hw2 : ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61199/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29158936739/1000000000000 : ℚ) : ℝ)
      = ((61199/1000000 : ℚ) : ℝ) * ((476461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c268 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((268 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((872011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55909869/20000000 : ℚ) : ℝ) ≤ Real.log ((268 : ℕ)) / 2 := by
    have h := (log_br_268).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((268 : ℕ)) / 2 ≤ ((5590987/2000000 : ℚ) : ℝ) := by
    have h := (log_br_268).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1023/8000) (δ := 3857/500000000) (ψ := 1641/200000) 301 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t268 : ((532634760967/10000000000000 : ℚ) : ℝ) ≤ stT301o2 268 := by
  have hc : ((871961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((268 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).1
  have hw2 : ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((532634760967/10000000000000 : ℚ) : ℝ)
      = ((610847/10000000 : ℚ) : ℝ) * ((871961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c269 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((269 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((998799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55947113/20000000 : ℚ) : ℝ) ≤ Real.log ((269 : ℕ)) / 2 := by
    have h := (log_br_269).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((269 : ℕ)) / 2 ≤ ((27973557/10000000 : ℚ) : ℝ) := by
    have h := (log_br_269).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 24511/2000000) (δ := 7539/1000000000) (ψ := 1641/200000) 301 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t269 : ((60894725279/1000000000000 : ℚ) : ℝ) ≤ stT301o2 269 := by
  have hc : ((998749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((269 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60894725279/1000000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((998749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c270 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((270 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((102637/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55984219/20000000 : ℚ) : ℝ) ≤ Real.log ((270 : ℕ)) / 2 := by
    have h := (log_br_270).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((270 : ℕ)) / 2 ≤ ((2799211/1000000 : ℚ) : ℝ) := by
    have h := (log_br_270).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 379667/2500000) (δ := 7639/1000000000) (ψ := 1641/200000) 301 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t270 : ((12491804367/250000000000 : ℚ) : ℝ) ≤ stT301o2 270 := by
  have hc : ((410523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((270 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12491804367/250000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((410523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c271 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((271 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((197903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14005297/5000000 : ℚ) : ℝ) ≤ Real.log ((271 : ℕ)) / 2 := by
    have h := (log_br_271).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((271 : ℕ)) / 2 ≤ ((56021189/20000000 : ℚ) : ℝ) := by
    have h := (log_br_271).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2909627/10000000) (δ := 1891/250000000) (ψ := 1641/200000) 301 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t271 : ((1878159037/78125000000 : ℚ) : ℝ) ≤ stT301o2 271 := by
  have hc : ((98939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((271 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1878159037/78125000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((98939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c272 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((272 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-146843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2802901/1000000 : ℚ) : ℝ) ≤ Real.log ((272 : ℕ)) / 2 := by
    have h := (log_br_272).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((272 : ℕ)) / 2 ≤ ((56058021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_272).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4295431/10000000) (δ := 1891/250000000) (ψ := 1641/200000) 301 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t272 : ((-4453355081/500000000000 : ℚ) : ℝ) ≤ stT301o2 272 := by
  have hc : ((-146893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((272 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4453355081/500000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-146893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c273 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((273 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-321981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56094717/20000000 : ℚ) : ℝ) ≤ Real.log ((273 : ℕ)) / 2 := by
    have h := (log_br_273).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((273 : ℕ)) / 2 ≤ ((28047359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_273).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1419039/2500000) (δ := 3857/500000000) (ψ := 1641/200000) 301 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t273 : ((-24360880921/625000000000 : ℚ) : ℝ) ≤ stT301o2 273 := by
  have hc : ((-161003/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((273 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24360880921/625000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-161003/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c274 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((274 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-94897/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56131281/20000000 : ℚ) : ℝ) ≤ Real.log ((274 : ℕ)) / 2 := by
    have h := (log_br_274).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((274 : ℕ)) / 2 ≤ ((28065641/10000000 : ℚ) : ℝ) := by
    have h := (log_br_274).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1762969/2500000) (δ := 7539/1000000000) (ψ := 1641/200000) 301 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t274 : ((-28666240473/500000000000 : ℚ) : ℝ) ≤ stT301o2 274 := by
  have hc : ((-47451/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((274 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28666240473/500000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-47451/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c275 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((275 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-974253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5616771/2000000 : ℚ) : ℝ) ≤ Real.log ((275 : ℕ)) / 2 := by
    have h := (log_br_275).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((275 : ℕ)) / 2 ≤ ((56167711/20000000 : ℚ) : ℝ) := by
    have h := (log_br_275).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3642723/5000000) (δ := 7571/1000000000) (ψ := 1641/200000) 301 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t275 : ((-587527117969/10000000000000 : ℚ) : ℝ) ≤ stT301o2 275 := by
  have hc : ((-974303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((275 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-587527117969/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-974303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c276 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((276 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-715331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7025501/2500000 : ℚ) : ℝ) ≤ Real.log ((276 : ℕ)) / 2 := by
    have h := (log_br_276).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((276 : ℕ)) / 2 ≤ ((56204009/20000000 : ℚ) : ℝ) := by
    have h := (log_br_276).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2959867/5000000) (δ := 3791/500000000) (ψ := 1641/200000) 301 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t276 : ((-43060928533/1000000000000 : ℚ) : ℝ) ≤ stT301o2 276 := by
  have hc : ((-715381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((276 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).2
  have h0 : (0:ℝ) ≤ ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43060928533/1000000000000 : ℚ) : ℝ)
      = ((60193/1000000 : ℚ) : ℝ) * ((-715381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c277 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((277 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-2501/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2249607/800000 : ℚ) : ℝ) ≤ Real.log ((277 : ℕ)) / 2 := by
    have h := (log_br_277).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((277 : ℕ)) / 2 ≤ ((3515011/1250000 : ℚ) : ℝ) := by
    have h := (log_br_277).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -91179/200000) (δ := 7721/1000000000) (ψ := 1641/200000) 301 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t277 : ((-1503006263/100000000000 : ℚ) : ℝ) ≤ stT301o2 277 := by
  have hc : ((-5003/20000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((277 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).2
  have h0 : (0:ℝ) ≤ ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1503006263/100000000000 : ℚ) : ℝ)
      = ((300421/5000000 : ℚ) : ℝ) * ((-5003/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c278 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((278 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((285529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56276211/20000000 : ℚ) : ℝ) ≤ Real.log ((278 : ℕ)) / 2 := by
    have h := (log_br_278).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((278 : ℕ)) / 2 ≤ ((14069053/5000000 : ℚ) : ℝ) := by
    have h := (log_br_278).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -400387/1250000) (δ := 1883/250000000) (ψ := 1641/200000) 301 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t278 : ((2140236063/125000000000 : ℚ) : ℝ) ≤ stT301o2 278 := by
  have hc : ((285479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((278 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2140236063/125000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((285479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c279 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((279 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((737893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56312117/20000000 : ℚ) : ℝ) ≤ Real.log ((279 : ℕ)) / 2 := by
    have h := (log_br_279).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((279 : ℕ)) / 2 ≤ ((28156059/10000000 : ℚ) : ℝ) := by
    have h := (log_br_279).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1852133/10000000) (δ := 477/62500000) (ψ := 1641/200000) 301 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t279 : ((110433699653/2500000000000 : ℚ) : ℝ) ≤ stT301o2 279 := by
  have hc : ((737843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((279 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110433699653/2500000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((737843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c280 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((280 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((979591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7043487/2500000 : ℚ) : ℝ) ≤ Real.log ((280 : ℕ)) / 2 := by
    have h := (log_br_280).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((280 : ℕ)) / 2 ≤ ((56347897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_280).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -126487/2500000) (δ := 3791/500000000) (ψ := 1641/200000) 301 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t280 : ((292693707587/5000000000000 : ℚ) : ℝ) ≤ stT301o2 280 := by
  have hc : ((979541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((280 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).1
  have hw2 : ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292693707587/5000000000000 : ℚ) : ℝ)
      = ((298807/5000000 : ℚ) : ℝ) * ((979541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c281 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((281 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((59043/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28191773/10000000 : ℚ) : ℝ) ≤ Real.log ((281 : ℕ)) / 2 := by
    have h := (log_br_281).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((281 : ℕ)) / 2 ≤ ((56383547/20000000 : ℚ) : ℝ) := by
    have h := (log_br_281).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 835383/10000000) (δ := 3841/500000000) (ψ := 1641/200000) 301 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t281 : ((281761427131/5000000000000 : ℚ) : ℝ) ≤ stT301o2 281 := by
  have hc : ((472319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((281 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).1
  have hw2 : ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((596549/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((281761427131/5000000000000 : ℚ) : ℝ)
      = ((596549/10000000 : ℚ) : ℝ) * ((472319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c282 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((282 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((645751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5641907/2000000 : ℚ) : ℝ) ≤ Real.log ((282 : ℕ)) / 2 := by
    have h := (log_br_282).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((282 : ℕ)) / 2 ≤ ((56419071/20000000 : ℚ) : ℝ) := by
    have h := (log_br_282).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1085987/5000000) (δ := 7571/1000000000) (ψ := 1641/200000) 301 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t282 : ((384509134191/10000000000000 : ℚ) : ℝ) ≤ stT301o2 282 := by
  have hc : ((645701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((282 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((384509134191/10000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((645701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c283 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((283 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((8423/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14113617/5000000 : ℚ) : ℝ) ≤ Real.log ((283 : ℕ)) / 2 := by
    have h := (log_br_283).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((283 : ℕ)) / 2 ≤ ((56454469/20000000 : ℚ) : ℝ) := by
    have h := (log_br_283).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 218989/625000) (δ := 7671/1000000000) (ψ := 1641/200000) 301 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t283 : ((5005465179/500000000000 : ℚ) : ℝ) ≤ stT301o2 283 := by
  have hc : ((16841/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((283 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5005465179/500000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((16841/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c284 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((284 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-176889/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28244871/10000000 : ℚ) : ℝ) ≤ Real.log ((284 : ℕ)) / 2 := by
    have h := (log_br_284).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((284 : ℕ)) / 2 ≤ ((56489743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_284).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 150969/312500) (δ := 7571/1000000000) (ψ := 1641/200000) 301 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t284 : ((-52489587687/2500000000000 : ℚ) : ℝ) ≤ stT301o2 284 := by
  have hc : ((-88457/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((284 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52489587687/2500000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-88457/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c285 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((285 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-777449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56524891/20000000 : ℚ) : ℝ) ≤ Real.log ((285 : ℕ)) / 2 := by
    have h := (log_br_285).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((285 : ℕ)) / 2 ≤ ((14131223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_285).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6153489/10000000) (δ := 1883/250000000) (ψ := 1641/200000) 301 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t285 : ((-460550755151/10000000000000 : ℚ) : ℝ) ≤ stT301o2 285 := by
  have hc : ((-777499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((285 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-460550755151/10000000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-777499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c286 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((286 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-123539/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28279959/10000000 : ℚ) : ℝ) ≤ Real.log ((286 : ℕ)) / 2 := by
    have h := (log_br_286).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((286 : ℕ)) / 2 ≤ ((56559919/20000000 : ℚ) : ℝ) := by
    have h := (log_br_286).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 373569/500000) (δ := 7571/1000000000) (ψ := 1641/200000) 301 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t286 : ((-292215649653/5000000000000 : ℚ) : ℝ) ≤ stT301o2 286 := by
  have hc : ((-494181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((286 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-292215649653/5000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-494181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c287 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((287 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-465753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28297411/10000000 : ℚ) : ℝ) ≤ Real.log ((287 : ℕ)) / 2 := by
    have h := (log_br_287).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((287 : ℕ)) / 2 ≤ ((56594823/20000000 : ℚ) : ℝ) := by
    have h := (log_br_287).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -173083/250000) (δ := 3839/500000000) (ψ := 1641/200000) 301 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t287 : ((-68735092349/1250000000000 : ℚ) : ℝ) ≤ stT301o2 287 := by
  have hc : ((-232889/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((287 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68735092349/1250000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-232889/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c288 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((288 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-312473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14157401/5000000 : ℚ) : ℝ) ≤ Real.log ((288 : ℕ)) / 2 := by
    have h := (log_br_288).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((288 : ℕ)) / 2 ≤ ((11325921/4000000 : ℚ) : ℝ) := by
    have h := (log_br_288).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -701831/1250000) (δ := 307/40000000) (ψ := 1641/200000) 301 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t288 : ((-11508832593/312500000000 : ℚ) : ℝ) ≤ stT301o2 288 := by
  have hc : ((-156249/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((288 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).2
  have h0 : (0:ℝ) ≤ ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11508832593/312500000000 : ℚ) : ℝ)
      = ((73657/1250000 : ℚ) : ℝ) * ((-156249/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c289 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((289 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-152799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28332133/10000000 : ℚ) : ℝ) ≤ Real.log ((289 : ℕ)) / 2 := by
    have h := (log_br_289).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((289 : ℕ)) / 2 ≤ ((56664267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_289).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -431049/1000000) (δ := 303/40000000) (ψ := 1641/200000) 301 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t289 : ((-22477821091/2500000000000 : ℚ) : ℝ) ≤ stT301o2 289 := by
  have hc : ((-152849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((289 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).2
  have h0 : (0:ℝ) ≤ ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22477821091/2500000000000 : ℚ) : ℝ)
      = ((147059/2500000 : ℚ) : ℝ) * ((-152849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c290 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((290 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((89581/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56698809/20000000 : ℚ) : ℝ) ≤ Real.log ((290 : ℕ)) / 2 := by
    have h := (log_br_290).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((290 : ℕ)) / 2 ≤ ((5669881/2000000 : ℚ) : ℝ) := by
    have h := (log_br_290).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -301081/1000000) (δ := 309/40000000) (ψ := 1641/200000) 301 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t290 : ((5259641457/250000000000 : ℚ) : ℝ) ≤ stT301o2 290 := by
  have hc : ((179137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((290 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5259641457/250000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((179137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c291 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((291 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((773623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3545827/1250000 : ℚ) : ℝ) ≤ Real.log ((291 : ℕ)) / 2 := by
    have h := (log_br_291).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((291 : ℕ)) / 2 ≤ ((56733233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_291).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -428911/2500000) (δ := 3789/500000000) (ψ := 1641/200000) 301 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t291 : ((45347622833/1000000000000 : ℚ) : ℝ) ≤ stT301o2 291 := by
  have hc : ((773573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((291 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45347622833/1000000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((773573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c292 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((292 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((985593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28383769/10000000 : ℚ) : ℝ) ≤ Real.log ((292 : ℕ)) / 2 := by
    have h := (log_br_292).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((292 : ℕ)) / 2 ≤ ((56767539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_292).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -424881/10000000) (δ := 303/40000000) (ψ := 1641/200000) 301 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t292 : ((115348938263/2000000000000 : ℚ) : ℝ) ≤ stT301o2 292 := by
  have hc : ((985543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((292 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115348938263/2000000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((985543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c293 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((293 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((470609/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28400863/10000000 : ℚ) : ℝ) ≤ Real.log ((293 : ℕ)) / 2 := by
    have h := (log_br_293).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((293 : ℕ)) / 2 ≤ ((56801727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_293).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 861443/10000000) (δ := 3839/500000000) (ψ := 1641/200000) 301 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t293 : ((17182374769/312500000000 : ℚ) : ℝ) ≤ stT301o2 293 := by
  have hc : ((58823/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((293 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17182374769/312500000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((58823/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c294 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((294 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((654447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56835797/20000000 : ℚ) : ℝ) ≤ Real.log ((294 : ℕ)) / 2 := by
    have h := (log_br_294).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((294 : ℕ)) / 2 ≤ ((28417899/10000000 : ℚ) : ℝ) := by
    have h := (log_br_294).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 535841/2500000) (δ := 941/125000000) (ψ := 1641/200000) 301 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t294 : ((381651528767/10000000000000 : ℚ) : ℝ) ≤ stT301o2 294 := by
  have hc : ((654397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((294 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).1
  have hw2 : ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((583211/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381651528767/10000000000000 : ℚ) : ℝ)
      = ((583211/10000000 : ℚ) : ℝ) * ((654397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c295 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((295 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((100517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56869753/20000000 : ℚ) : ℝ) ≤ Real.log ((295 : ℕ)) / 2 := by
    have h := (log_br_295).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((295 : ℕ)) / 2 ≤ ((28434877/10000000 : ℚ) : ℝ) := by
    have h := (log_br_295).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1710479/5000000) (δ := 309/40000000) (ψ := 1641/200000) 301 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t295 : ((7313581653/625000000000 : ℚ) : ℝ) ≤ stT301o2 295 := by
  have hc : ((25123/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((295 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7313581653/625000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((25123/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c296 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((296 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-302099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28451797/10000000 : ℚ) : ℝ) ≤ Real.log ((296 : ℕ)) / 2 := by
    have h := (log_br_296).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((296 : ℕ)) / 2 ≤ ((11380719/4000000 : ℚ) : ℝ) := by
    have h := (log_br_296).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2347113/5000000) (δ := 303/40000000) (ψ := 1641/200000) 301 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t296 : ((-175620782611/10000000000000 : ℚ) : ℝ) ≤ stT301o2 296 := by
  have hc : ((-302149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((296 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175620782611/10000000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-302149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c297 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((297 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-181843/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56937321/20000000 : ℚ) : ℝ) ≤ Real.log ((297 : ℕ)) / 2 := by
    have h := (log_br_297).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((297 : ℕ)) / 2 ≤ ((28468661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_297).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1490801/2500000) (δ := 309/40000000) (ψ := 1641/200000) 301 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t297 : ((-211046581149/5000000000000 : ℚ) : ℝ) ≤ stT301o2 297 := by
  have hc : ((-363711/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((297 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-211046581149/5000000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-363711/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c298 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((298 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-193761/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28485467/10000000 : ℚ) : ℝ) ≤ Real.log ((298 : ℕ)) / 2 := by
    have h := (log_br_298).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((298 : ℕ)) / 2 ≤ ((11394187/4000000 : ℚ) : ℝ) := by
    have h := (log_br_298).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3613947/5000000) (δ := 3839/500000000) (ψ := 1641/200000) 301 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t298 : ((-22449726747/400000000000 : ℚ) : ℝ) ≤ stT301o2 298 := by
  have hc : ((-193771/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((298 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22449726747/400000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-193771/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c299 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((299 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-967977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11400887/4000000 : ℚ) : ℝ) ≤ Real.log ((299 : ℕ)) / 2 := by
    have h := (log_br_299).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((299 : ℕ)) / 2 ≤ ((14251109/5000000 : ℚ) : ℝ) := by
    have h := (log_br_299).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1443919/2000000) (δ := 3859/500000000) (ψ := 1641/200000) 301 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t299 : ((-111964906901/2000000000000 : ℚ) : ℝ) ≤ stT301o2 299 := by
  have hc : ((-968027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((299 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111964906901/2000000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-968027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c300 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((300 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-45463/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((222804/78125 : ℚ) : ℝ) ≤ Real.log ((300 : ℕ)) / 2 := by
    have h := (log_br_300).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((300 : ℕ)) / 2 ≤ ((2281513/800000 : ℚ) : ℝ) := by
    have h := (log_br_300).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5963333/10000000) (δ := 1537/200000000) (ψ := 1641/200000) 301 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t300 : ((-209999301879/5000000000000 : ℚ) : ℝ) ≤ stT301o2 300 := by
  have hc : ((-363729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((300 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209999301879/5000000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-363729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c301 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((301 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-308583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28535551/10000000 : ℚ) : ℝ) ≤ Real.log ((301 : ℕ)) / 2 := by
    have h := (log_br_301).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((301 : ℕ)) / 2 ≤ ((57071103/20000000 : ℚ) : ℝ) := by
    have h := (log_br_301).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4711249/10000000) (δ := 1917/250000000) (ψ := 1641/200000) 301 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t301 : ((-177893283503/10000000000000 : ℚ) : ℝ) ≤ stT301o2 301 := by
  have hc : ((-308633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((301 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177893283503/10000000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-308633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c302 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((302 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((92207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5710427/2000000 : ℚ) : ℝ) ≤ Real.log ((302 : ℕ)) / 2 := by
    have h := (log_br_302).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((302 : ℕ)) / 2 ≤ ((57104271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_302).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3463303/10000000) (δ := 1917/250000000) (ψ := 1641/200000) 301 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t302 : ((5304474917/500000000000 : ℚ) : ℝ) ≤ stT301o2 302 := by
  have hc : ((46091/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((302 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5304474917/500000000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((46091/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c303 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((303 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((315561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3571083/1250000 : ℚ) : ℝ) ≤ Real.log ((303 : ℕ)) / 2 := by
    have h := (log_br_303).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((303 : ℕ)) / 2 ≤ ((57137329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_303).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -443899/2000000) (δ := 1537/200000000) (ψ := 1641/200000) 301 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t303 : ((2832349741/78125000000 : ℚ) : ℝ) ≤ stT301o2 303 := by
  have hc : ((19721/31250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((303 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2832349741/78125000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((19721/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c304 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((304 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((924179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57170277/20000000 : ℚ) : ℝ) ≤ Real.log ((304 : ℕ)) / 2 := by
    have h := (log_br_304).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((304 : ℕ)) / 2 ≤ ((28585139/10000000 : ℚ) : ℝ) := by
    have h := (log_br_304).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -979789/10000000) (δ := 1527/200000000) (ψ := 1641/200000) 301 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t304 : ((530024022531/10000000000000 : ℚ) : ℝ) ≤ stT301o2 304 := by
  have hc : ((924129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((304 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).1
  have hw2 : ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((530024022531/10000000000000 : ℚ) : ℝ)
      = ((573539/10000000 : ℚ) : ℝ) * ((924129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c305 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((305 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((994769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57203117/20000000 : ℚ) : ℝ) ≤ Real.log ((305 : ℕ)) / 2 := by
    have h := (log_br_305).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((305 : ℕ)) / 2 ≤ ((28601559/10000000 : ℚ) : ℝ) := by
    have h := (log_br_305).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 31977/1250000) (δ := 1527/200000000) (ψ := 1641/200000) 301 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t305 : ((284787054981/5000000000000 : ℚ) : ℝ) ≤ stT301o2 305 := by
  have hc : ((994719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((305 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284787054981/5000000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((994719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c306 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((306 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((207041/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57235851/20000000 : ℚ) : ℝ) ≤ Real.log ((306 : ℕ)) / 2 := by
    have h := (log_br_306).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((306 : ℕ)) / 2 ≤ ((14308963/5000000 : ℚ) : ℝ) := by
    have h := (log_br_306).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 185929/1250000) (δ := 3859/500000000) (ψ := 1641/200000) 301 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t306 : ((236700238677/5000000000000 : ℚ) : ℝ) ≤ stT301o2 306 := by
  have hc : ((414057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((306 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236700238677/5000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((414057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c307 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((307 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((466033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57268477/20000000 : ℚ) : ℝ) ≤ Real.log ((307 : ℕ)) / 2 := by
    have h := (log_br_307).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((307 : ℕ)) / 2 ≤ ((28634239/10000000 : ℚ) : ℝ) := by
    have h := (log_br_307).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1357493/5000000) (δ := 1527/200000000) (ψ := 1641/200000) 301 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t307 : ((26595047759/1000000000000 : ℚ) : ℝ) ≤ stT301o2 307 := by
  have hc : ((465983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((307 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26595047759/1000000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((465983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c308 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((308 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-289/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57300997/20000000 : ℚ) : ℝ) ≤ Real.log ((308 : ℕ)) / 2 := by
    have h := (log_br_308).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((308 : ℕ)) / 2 ≤ ((28650499/10000000 : ℚ) : ℝ) := by
    have h := (log_br_308).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3938551/10000000) (δ := 1527/200000000) (ψ := 1641/200000) 301 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t308 : ((-1331629611/5000000000000 : ℚ) : ℝ) ≤ stT301o2 308 := by
  have hc : ((-2337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((308 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).2
  have h0 : (0:ℝ) ≤ ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1331629611/5000000000000 : ℚ) : ℝ)
      = ((569803/10000000 : ℚ) : ℝ) * ((-2337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c309 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((309 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-118201/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14333353/5000000 : ℚ) : ℝ) ≤ Real.log ((309 : ℕ)) / 2 := by
    have h := (log_br_309).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((309 : ℕ)) / 2 ≤ ((57333413/20000000 : ℚ) : ℝ) := by
    have h := (log_br_309).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1031633/2000000) (δ := 473/62500000) (ψ := 1641/200000) 301 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t309 : ((-134498828187/5000000000000 : ℚ) : ℝ) ≤ stT301o2 309 := by
  have hc : ((-236427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((309 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134498828187/5000000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-236427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c310 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((310 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-25931/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28682861/10000000 : ℚ) : ℝ) ≤ Real.log ((310 : ℕ)) / 2 := by
    have h := (log_br_310).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((310 : ℕ)) / 2 ≤ ((57365723/20000000 : ℚ) : ℝ) := by
    have h := (log_br_310).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6373829/10000000) (δ := 1517/200000000) (ψ := 1641/200000) 301 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t310 : ((-117829680501/2500000000000 : ℚ) : ℝ) ≤ stT301o2 310 := by
  have hc : ((-414921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((310 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117829680501/2500000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-414921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c311 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((311 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-248561/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57397929/20000000 : ℚ) : ℝ) ≤ Real.log ((311 : ℕ)) / 2 := by
    have h := (log_br_311).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((311 : ℕ)) / 2 ≤ ((5739793/2000000 : ℚ) : ℝ) := by
    have h := (log_br_311).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7585617/10000000) (δ := 3809/500000000) (ψ := 1641/200000) 301 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t311 : ((-35238276507/625000000000 : ℚ) : ℝ) ≤ stT301o2 311 := by
  have hc : ((-497147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((311 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35238276507/625000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-497147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c312 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((312 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-465109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57430031/20000000 : ℚ) : ℝ) ≤ Real.log ((312 : ℕ)) / 2 := by
    have h := (log_br_312).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((312 : ℕ)) / 2 ≤ ((3589377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_312).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1728627/2500000) (δ := 3821/500000000) (ψ := 1641/200000) 301 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t312 : ((-131665248813/2500000000000 : ℚ) : ℝ) ≤ stT301o2 312 := by
  have hc : ((-232567/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((312 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131665248813/2500000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-232567/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c313 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((313 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-327207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57462031/20000000 : ℚ) : ℝ) ≤ Real.log ((313 : ℕ)) / 2 := by
    have h := (log_br_313).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((313 : ℕ)) / 2 ≤ ((3591377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_313).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1427627/2500000) (δ := 3821/500000000) (ψ := 1641/200000) 301 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t313 : ((-1445020721/39062500000 : ℚ) : ℝ) ≤ stT301o2 313 := by
  have hc : ((-10226/15625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((313 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1445020721/39062500000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-10226/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c314 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((314 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-23123/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57493929/20000000 : ℚ) : ℝ) ≤ Real.log ((314 : ℕ)) / 2 := by
    have h := (log_br_314).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((314 : ℕ)) / 2 ≤ ((5749393/2000000 : ℚ) : ℝ) := by
    have h := (log_br_314).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2255173/5000000) (δ := 3771/500000000) (ψ := 1641/200000) 301 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t314 : ((-1631486703/125000000000 : ℚ) : ℝ) ≤ stT301o2 314 := by
  have hc : ((-2891/12500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((314 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1631486703/125000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-2891/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c315 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((315 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((242753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28762863/10000000 : ℚ) : ℝ) ≤ Real.log ((315 : ℕ)) / 2 := by
    have h := (log_br_315).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((315 : ℕ)) / 2 ≤ ((57525727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_315).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -51781/156250) (δ := 7561/1000000000) (ψ := 1641/200000) 301 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t315 : ((34186901877/2500000000000 : ℚ) : ℝ) ≤ stT301o2 315 := by
  have hc : ((242703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((315 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34186901877/2500000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((242703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c316 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((316 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((330529/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28778711/10000000 : ℚ) : ℝ) ≤ Real.log ((316 : ℕ)) / 2 := by
    have h := (log_br_316).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((316 : ℕ)) / 2 ≤ ((57557423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_316).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1060711/5000000) (δ := 7561/1000000000) (ψ := 1641/200000) 301 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t316 : ((23240338959/625000000000 : ℚ) : ℝ) ≤ stT301o2 316 := by
  have hc : ((41313/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((316 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23240338959/625000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((41313/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c317 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((317 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((186243/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57589017/20000000 : ℚ) : ℝ) ≤ Real.log ((317 : ℕ)) / 2 := by
    have h := (log_br_317).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((317 : ℕ)) / 2 ≤ ((28794509/10000000 : ℚ) : ℝ) := by
    have h := (log_br_317).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -46633/500000) (δ := 3771/500000000) (ψ := 1641/200000) 301 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t317 : ((20919739123/400000000000 : ℚ) : ℝ) ≤ stT301o2 317 := by
  have hc : ((186233/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((317 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20919739123/400000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((186233/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c318 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((318 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((994909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57620513/20000000 : ℚ) : ℝ) ≤ Real.log ((318 : ℕ)) / 2 := by
    have h := (log_br_318).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((318 : ℕ)) / 2 ≤ ((28810257/10000000 : ℚ) : ℝ) := by
    have h := (log_br_318).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 252377/10000000) (δ := 3771/500000000) (ψ := 1641/200000) 301 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t318 : ((139472267787/2500000000000 : ℚ) : ℝ) ≤ stT301o2 318 := by
  have hc : ((994859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((318 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139472267787/2500000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((994859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c319 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((319 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((210003/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57651911/20000000 : ℚ) : ℝ) ≤ Real.log ((319 : ℕ)) / 2 := by
    have h := (log_br_319).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((319 : ℕ)) / 2 ≤ ((7206489/2500000 : ℚ) : ℝ) := by
    have h := (log_br_319).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1433727/10000000) (δ := 3821/500000000) (ψ := 1641/200000) 301 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t319 : ((58786000513/1250000000000 : ℚ) : ℝ) ≤ stT301o2 319 := by
  have hc : ((419981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((319 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).1
  have hw2 : ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((139973/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58786000513/1250000000000 : ℚ) : ℝ)
      = ((139973/2500000 : ℚ) : ℝ) * ((419981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c320 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((320 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((62789/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57683209/20000000 : ℚ) : ℝ) ≤ Real.log ((320 : ℕ)) / 2 := by
    have h := (log_br_320).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((320 : ℕ)) / 2 ≤ ((5768321/2000000 : ℚ) : ℝ) := by
    have h := (log_br_320).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1305657/5000000) (δ := 3771/500000000) (ψ := 1641/200000) 301 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t320 : ((17548280887/625000000000 : ℚ) : ℝ) ≤ stT301o2 320 := by
  have hc : ((251131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((320 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17548280887/625000000000 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((251131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c321 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((321 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((1133/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57714411/20000000 : ℚ) : ℝ) ≤ Real.log ((321 : ℕ)) / 2 := by
    have h := (log_br_321).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((321 : ℕ)) / 2 ≤ ((14428603/5000000 : ℚ) : ℝ) := by
    have h := (log_br_321).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3785289/10000000) (δ := 7611/1000000000) (ψ := 1641/200000) 301 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t321 : ((31591007/10000000000 : ℚ) : ℝ) ≤ stT301o2 321 := by
  have hc : ((283/5000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((321 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31591007/10000000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((283/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c322 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((322 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-15997/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11549103/4000000 : ℚ) : ℝ) ≤ Real.log ((322 : ℕ)) / 2 := by
    have h := (log_br_322).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((322 : ℕ)) / 2 ≤ ((14436379/5000000 : ℚ) : ℝ) := by
    have h := (log_br_322).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4955577/10000000) (δ := 7611/1000000000) (ψ := 1641/200000) 301 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t322 : ((-8915906721/400000000000 : ℚ) : ℝ) ≤ stT301o2 322 := by
  have hc : ((-15999/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((322 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8915906721/400000000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-15999/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c323 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((323 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-76953/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57776523/20000000 : ℚ) : ℝ) ≤ Real.log ((323 : ℕ)) / 2 := by
    have h := (log_br_323).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((323 : ℕ)) / 2 ≤ ((14444131/5000000 : ℚ) : ℝ) := by
    have h := (log_br_323).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6122253/10000000) (δ := 7611/1000000000) (ψ := 1641/200000) 301 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t323 : ((-4282058557/100000000000 : ℚ) : ℝ) ≤ stT301o2 323 := by
  have hc : ((-38479/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((323 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4282058557/100000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-38479/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c324 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((324 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-974241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11561487/4000000 : ℚ) : ℝ) ≤ Real.log ((324 : ℕ)) / 2 := by
    have h := (log_br_324).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((324 : ℕ)) / 2 ≤ ((14451859/5000000 : ℚ) : ℝ) := by
    have h := (log_br_324).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7285317/10000000) (δ := 7611/1000000000) (ψ := 1641/200000) 301 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t324 : ((-135318302699/2500000000000 : ℚ) : ℝ) ≤ stT301o2 324 := by
  have hc : ((-974291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((324 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135318302699/2500000000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-974291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c325 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((325 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-972207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57838251/20000000 : ℚ) : ℝ) ≤ Real.log ((325 : ℕ)) / 2 := by
    have h := (log_br_325).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((325 : ℕ)) / 2 ≤ ((14459563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_325).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3631597/5000000) (δ := 7549/1000000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t325 : ((-539311930157/10000000000000 : ℚ) : ℝ) ≤ stT301o2 325 := by
  have hc : ((-972257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((325 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-539311930157/10000000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-972257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c326 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((326 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-765691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57868973/20000000 : ℚ) : ℝ) ≤ Real.log ((326 : ℕ)) / 2 := by
    have h := (log_br_326).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((326 : ℕ)) / 2 ≤ ((28934487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_326).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6107279/10000000) (δ := 1901/250000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t326 : ((-424104887109/10000000000000 : ℚ) : ℝ) ≤ stT301o2 326 := by
  have hc : ((-765741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((326 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-424104887109/10000000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-765741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c327 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((327 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-99919/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57899601/20000000 : ℚ) : ℝ) ≤ Real.log ((327 : ℕ)) / 2 := by
    have h := (log_br_327).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((327 : ℕ)) / 2 ≤ ((28949801/10000000 : ℚ) : ℝ) := by
    have h := (log_br_327).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -49549/100000) (δ := 7649/1000000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t327 : ((-55262319363/2500000000000 : ℚ) : ℝ) ≤ stT301o2 327 := by
  have hc : ((-199863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((327 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55262319363/2500000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-199863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c328 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((328 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((48369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7241267/2500000 : ℚ) : ℝ) ≤ Real.log ((328 : ℕ)) / 2 := by
    have h := (log_br_328).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((328 : ℕ)) / 2 ≤ ((57930137/20000000 : ℚ) : ℝ) := by
    have h := (log_br_328).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3806021/10000000) (δ := 3777/500000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t328 : ((26679674083/10000000000000 : ℚ) : ℝ) ≤ stT301o2 328 := by
  have hc : ((48319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((328 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26679674083/10000000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((48319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c329 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((329 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((242571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57960577/20000000 : ℚ) : ℝ) ≤ Real.log ((329 : ℕ)) / 2 := by
    have h := (log_br_329).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((329 : ℕ)) / 2 ≤ ((28980289/10000000 : ℚ) : ℝ) := by
    have h := (log_br_329).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1330339/5000000) (δ := 7649/1000000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t329 : ((66859866541/2500000000000 : ℚ) : ℝ) ≤ stT301o2 329 := by
  have hc : ((121273/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((329 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66859866541/2500000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((121273/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c330 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((330 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((821067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28995463/10000000 : ℚ) : ℝ) ≤ Real.log ((330 : ℕ)) / 2 := by
    have h := (log_br_330).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((330 : ℕ)) / 2 ≤ ((57990927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_330).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1518797/10000000) (δ := 7599/1000000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t330 : ((451954259177/10000000000000 : ℚ) : ℝ) ≤ stT301o2 330 := by
  have hc : ((821017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((330 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((451954259177/10000000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((821017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c331 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((331 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((988447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58021183/20000000 : ℚ) : ℝ) ≤ Real.log ((331 : ℕ)) / 2 := by
    have h := (log_br_331).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((331 : ℕ)) / 2 ≤ ((906581/312500 : ℚ) : ℝ) := by
    have h := (log_br_331).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -190189/5000000) (δ := 963/125000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t331 : ((543271422653/10000000000000 : ℚ) : ℝ) ≤ stT301o2 331 := by
  have hc : ((988397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((331 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).1
  have hw2 : ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((549649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((543271422653/10000000000000 : ℚ) : ℝ)
      = ((549649/10000000 : ℚ) : ℝ) * ((988397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c332 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((332 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((954789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58051349/20000000 : ℚ) : ℝ) ≤ Real.log ((332 : ℕ)) / 2 := by
    have h := (log_br_332).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((332 : ℕ)) / 2 ≤ ((1161027/400000 : ℚ) : ℝ) := by
    have h := (log_br_332).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 377309/5000000) (δ := 1901/250000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t332 : ((523980812719/10000000000000 : ℚ) : ℝ) ≤ stT301o2 332 := by
  have hc : ((954739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((332 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((523980812719/10000000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((954739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c333 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((333 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((728631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3630089/1250000 : ℚ) : ℝ) ≤ Real.log ((333 : ℕ)) / 2 := by
    have h := (log_br_333).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((333 : ℕ)) / 2 ≤ ((2323257/800000 : ℚ) : ℝ) := by
    have h := (log_br_333).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 188619/1000000) (δ := 3777/500000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t333 : ((99814868419/2500000000000 : ℚ) : ℝ) ≤ stT301o2 333 := by
  have hc : ((728581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((333 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99814868419/2500000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((728581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c334 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((334 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((5578/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58111409/20000000 : ℚ) : ℝ) ≤ Real.log ((334 : ℕ)) / 2 := by
    have h := (log_br_334).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((334 : ℕ)) / 2 ≤ ((5811141/2000000 : ℚ) : ℝ) := by
    have h := (log_br_334).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 376797/1250000) (δ := 7649/1000000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t334 : ((3906194777/200000000000 : ℚ) : ℝ) ≤ stT301o2 334 := by
  have hc : ((178471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((334 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3906194777/200000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((178471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c335 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((335 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-84787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11628261/4000000 : ℚ) : ℝ) ≤ Real.log ((335 : ℕ)) / 2 := by
    have h := (log_br_335).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((335 : ℕ)) / 2 ≤ ((29070653/10000000 : ℚ) : ℝ) := by
    have h := (log_br_335).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4139213/10000000) (δ := 7649/1000000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t335 : ((-46351458483/10000000000000 : ℚ) : ℝ) ≤ stT301o2 335 := by
  have hc : ((-84837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((335 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46351458483/10000000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-84837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c336 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((336 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-508523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58171111/20000000 : ℚ) : ℝ) ≤ Real.log ((336 : ℕ)) / 2 := by
    have h := (log_br_336).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((336 : ℕ)) / 2 ≤ ((7271389/2500000 : ℚ) : ℝ) := by
    have h := (log_br_336).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5260663/10000000) (δ := 963/125000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t336 : ((-55489891457/2000000000000 : ℚ) : ℝ) ≤ stT301o2 336 := by
  have hc : ((-508573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((336 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55489891457/2000000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-508573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c337 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((337 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-830901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58200829/20000000 : ℚ) : ℝ) ≤ Real.log ((337 : ℕ)) / 2 := by
    have h := (log_br_337).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((337 : ℕ)) / 2 ≤ ((5820083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_337).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6378803/10000000) (δ := 1901/250000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t337 : ((-90529618597/2000000000000 : ℚ) : ℝ) ≤ stT301o2 337 := by
  have hc : ((-830951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((337 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90529618597/2000000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-830951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c338 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((338 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-247407/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29115229/10000000 : ℚ) : ℝ) ≤ Real.log ((338 : ℕ)) / 2 := by
    have h := (log_br_338).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((338 : ℕ)) / 2 ≤ ((58230459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_338).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3746797/5000000) (δ := 3827/500000000) (ψ := 1641/200000) 301 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t338 : ((-269157282431/5000000000000 : ℚ) : ℝ) ≤ stT301o2 338 := by
  have hc : ((-494839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((338 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269157282431/5000000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-494839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c339 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((339 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-477599/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58260001/20000000 : ℚ) : ℝ) ≤ Real.log ((339 : ℕ)) / 2 := by
    have h := (log_br_339).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((339 : ℕ)) / 2 ≤ ((29130001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_339).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3551407/5000000) (δ := 481/62500000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t339 : ((-16213125789/312500000000 : ℚ) : ℝ) ≤ stT301o2 339 := by
  have hc : ((-59703/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((339 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16213125789/312500000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-59703/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c340 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((340 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-29437/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3643091/1250000 : ℚ) : ℝ) ≤ Real.log ((340 : ℕ)) / 2 := by
    have h := (log_br_340).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((340 : ℕ)) / 2 ≤ ((58289457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_340).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5994569/10000000) (δ := 7607/1000000000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t340 : ((-15965564553/400000000000 : ℚ) : ℝ) ≤ stT301o2 340 := by
  have hc : ((-29439/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((340 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15965564553/400000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-29439/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c341 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((341 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-375599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7289853/2500000 : ℚ) : ℝ) ≤ Real.log ((341 : ℕ)) / 2 := by
    have h := (log_br_341).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((341 : ℕ)) / 2 ≤ ((2332753/800000 : ℚ) : ℝ) := by
    have h := (log_br_341).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2444799/5000000) (δ := 7607/1000000000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t341 : ((-203425578619/10000000000000 : ℚ) : ℝ) ≤ stT301o2 341 := by
  have hc : ((-375649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((341 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203425578619/10000000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-375649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c342 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((342 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((27819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58348107/20000000 : ℚ) : ℝ) ≤ Real.log ((342 : ℕ)) / 2 := by
    have h := (log_br_342).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((342 : ℕ)) / 2 ≤ ((14587027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_342).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -151513/400000) (δ := 7657/1000000000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t342 : ((3757317993/1250000000000 : ℚ) : ℝ) ≤ stT301o2 342 := by
  have hc : ((13897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((342 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3757317993/1250000000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((13897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c343 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((343 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((475103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7297163/2500000 : ℚ) : ℝ) ≤ Real.log ((343 : ℕ)) / 2 := by
    have h := (log_br_343).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((343 : ℕ)) / 2 ≤ ((11675461/4000000 : ℚ) : ℝ) := by
    have h := (log_br_343).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -336161/1250000) (δ := 7607/1000000000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t343 : ((256504392297/10000000000000 : ℚ) : ℝ) ≤ stT301o2 343 := by
  have hc : ((475053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((343 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((256504392297/10000000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((475053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c344 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((344 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((803539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3650401/1250000 : ℚ) : ℝ) ≤ Real.log ((344 : ℕ)) / 2 := by
    have h := (log_br_344).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((344 : ℕ)) / 2 ≤ ((58406417/20000000 : ℚ) : ℝ) := by
    have h := (log_br_344).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1593949/10000000) (δ := 7607/1000000000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t344 : ((433211539707/10000000000000 : ℚ) : ℝ) ≤ stT301o2 344 := by
  have hc : ((803489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((344 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((433211539707/10000000000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((803489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c345 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((345 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((489963/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14608861/5000000 : ℚ) : ℝ) ≤ Real.log ((345 : ℕ)) / 2 := by
    have h := (log_br_345).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((345 : ℕ)) / 2 ≤ ((11687089/4000000 : ℚ) : ℝ) := by
    have h := (log_br_345).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -501771/10000000) (δ := 3823/500000000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t345 : ((131886655189/2500000000000 : ℚ) : ℝ) ≤ stT301o2 345 := by
  have hc : ((244969/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((345 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131886655189/2500000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((244969/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c346 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((346 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((972541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58464387/20000000 : ℚ) : ℝ) ≤ Real.log ((346 : ℕ)) / 2 := by
    have h := (log_br_346).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((346 : ℕ)) / 2 ≤ ((14616097/5000000 : ℚ) : ℝ) := by
    have h := (log_br_346).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 58721/1000000) (δ := 7657/1000000000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t346 : ((522814079073/10000000000000 : ℚ) : ℝ) ≤ stT301o2 346 := by
  have hc : ((972491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((346 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((522814079073/10000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((972491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c347 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((347 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((392151/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58493247/20000000 : ℚ) : ℝ) ≤ Real.log ((347 : ℕ)) / 2 := by
    have h := (log_br_347).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((347 : ℕ)) / 2 ≤ ((913957/312500 : ℚ) : ℝ) := by
    have h := (log_br_347).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1673067/10000000) (δ := 1899/250000000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t347 : ((26313027041/625000000000 : ℚ) : ℝ) ≤ stT301o2 347 := by
  have hc : ((196063/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((347 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26313027041/625000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((196063/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c348 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((348 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((451527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7315253/2500000 : ℚ) : ℝ) ≤ Real.log ((348 : ℕ)) / 2 := by
    have h := (log_br_348).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((348 : ℕ)) / 2 ≤ ((2340881/800000 : ℚ) : ℝ) := by
    have h := (log_br_348).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1377901/5000000) (δ := 7607/1000000000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t348 : ((30252119339/1250000000000 : ℚ) : ℝ) ≤ stT301o2 348 := by
  have hc : ((451477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((348 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30252119339/1250000000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((451477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c349 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((349 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((572/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58550719/20000000 : ℚ) : ℝ) ≤ Real.log ((349 : ℕ)) / 2 := by
    have h := (log_br_349).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((349 : ℕ)) / 2 ≤ ((182971/62500 : ℚ) : ℝ) := by
    have h := (log_br_349).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3835451/10000000) (δ := 1899/250000000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t349 : ((9784511073/5000000000000 : ℚ) : ℝ) ≤ stT301o2 349 := by
  have hc : ((18279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((349 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9784511073/5000000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((18279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c350 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((350 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-9597/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58579331/20000000 : ℚ) : ℝ) ≤ Real.log ((350 : ℕ)) / 2 := by
    have h := (log_br_350).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((350 : ℕ)) / 2 ≤ ((14644833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_350).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2455989/5000000) (δ := 7657/1000000000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t350 : ((-20521941539/1000000000000 : ℚ) : ℝ) ≤ stT301o2 350 := by
  have hc : ((-38393/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((350 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20521941539/1000000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-38393/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c351 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((351 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-183363/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29303931/10000000 : ℚ) : ℝ) ≤ Real.log ((351 : ℕ)) / 2 := by
    have h := (log_br_351).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((351 : ℕ)) / 2 ≤ ((58607863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_351).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5985457/10000000) (δ := 7707/1000000000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t351 : ((-195757380511/5000000000000 : ℚ) : ℝ) ≤ stT301o2 351 := by
  have hc : ((-366751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((351 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195757380511/5000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-366751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c352 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((352 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-94947/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58636311/20000000 : ℚ) : ℝ) ≤ Real.log ((352 : ℕ)) / 2 := by
    have h := (log_br_352).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((352 : ℕ)) / 2 ≤ ((7329539/2500000 : ℚ) : ℝ) := by
    have h := (log_br_352).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 141117/200000) (δ := 1899/250000000) (ψ := 1641/200000) 301 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t352 : ((-3163100369/62500000000 : ℚ) : ℝ) ≤ stT301o2 352 := by
  have hc : ((-11869/12500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((352 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3163100369/62500000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-11869/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c353 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((353 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-497103/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1466617/500000 : ℚ) : ℝ) ≤ Real.log ((353 : ℕ)) / 2 := by
    have h := (log_br_353).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((353 : ℕ)) / 2 ≤ ((58664681/20000000 : ℚ) : ℝ) := by
    have h := (log_br_353).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7584729/10000000) (δ := 3857/500000000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t353 : ((-33074360827/625000000000 : ℚ) : ℝ) ≤ stT301o2 353 := by
  have hc : ((-62141/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((353 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33074360827/625000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-62141/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c354 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((354 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-430529/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58692969/20000000 : ℚ) : ℝ) ≤ Real.log ((354 : ℕ)) / 2 := by
    have h := (log_br_354).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((354 : ℕ)) / 2 ≤ ((5869297/2000000 : ℚ) : ℝ) := by
    have h := (log_br_354).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1630089/2500000) (δ := 7589/1000000000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t354 : ((-22883729823/500000000000 : ℚ) : ℝ) ≤ stT301o2 354 := by
  have hc : ((-215277/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((354 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22883729823/500000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-215277/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c355 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((355 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-575173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58721177/20000000 : ℚ) : ℝ) ≤ Real.log ((355 : ℕ)) / 2 := by
    have h := (log_br_355).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((355 : ℕ)) / 2 ≤ ((29360589/10000000 : ℚ) : ℝ) := by
    have h := (log_br_355).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -545903/1000000) (δ := 7589/1000000000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t355 : ((-61059346227/2000000000000 : ℚ) : ℝ) ≤ stT301o2 355 := by
  have hc : ((-575223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((355 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61059346227/2000000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-575223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c356 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((356 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-23541/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58749307/20000000 : ℚ) : ℝ) ≤ Real.log ((356 : ℕ)) / 2 := by
    have h := (log_br_356).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((356 : ℕ)) / 2 ≤ ((14687327/5000000 : ℚ) : ℝ) := by
    have h := (log_br_356).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4400639/10000000) (δ := 7689/1000000000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t356 : ((-49920075811/5000000000000 : ℚ) : ℝ) ≤ stT301o2 356 := by
  have hc : ((-94189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((356 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49920075811/5000000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-94189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c357 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((357 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((230599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58777357/20000000 : ℚ) : ℝ) ≤ Real.log ((357 : ℕ)) / 2 := by
    have h := (log_br_357).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((357 : ℕ)) / 2 ≤ ((29388679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_357).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3345257/10000000) (δ := 479/62500000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t357 : ((15252430193/1250000000000 : ℚ) : ℝ) ≤ stT301o2 357 := by
  have hc : ((230549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((357 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15252430193/1250000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((230549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c358 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((358 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((121621/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58805329/20000000 : ℚ) : ℝ) ≤ Real.log ((358 : ℕ)) / 2 := by
    have h := (log_br_358).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((358 : ℕ)) / 2 ≤ ((5880533/2000000 : ℚ) : ℝ) := by
    have h := (log_br_358).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2292811/10000000) (δ := 7589/1000000000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t358 : ((16068339819/500000000000 : ℚ) : ℝ) ≤ stT301o2 358 := by
  have hc : ((121611/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((358 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16068339819/500000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((121611/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c359 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((359 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((54929/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58833223/20000000 : ℚ) : ℝ) ≤ Real.log ((359 : ℕ)) / 2 := by
    have h := (log_br_359).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((359 : ℕ)) / 2 ≤ ((7354153/2500000 : ℚ) : ℝ) := by
    have h := (log_br_359).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1243299/10000000) (δ := 1891/250000000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t359 : ((231909787053/5000000000000 : ℚ) : ℝ) ≤ stT301o2 359 := by
  have hc : ((439407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((359 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231909787053/5000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((439407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c360 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((360 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((996907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((735763/250000 : ℚ) : ℝ) ≤ Real.log ((360 : ℕ)) / 2 := by
    have h := (log_br_360).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((360 : ℕ)) / 2 ≤ ((58861041/20000000 : ℚ) : ℝ) := by
    have h := (log_br_360).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -49171/2500000) (δ := 3857/500000000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t360 : ((262694747211/5000000000000 : ℚ) : ℝ) ≤ stT301o2 360 := by
  have hc : ((996857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((360 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((262694747211/5000000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((996857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c361 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((361 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((188631/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58888779/20000000 : ℚ) : ℝ) ≤ Real.log ((361 : ℕ)) / 2 := by
    have h := (log_br_361).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((361 : ℕ)) / 2 ≤ ((2944439/1000000 : ℚ) : ℝ) := by
    have h := (log_br_361).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 169399/2000000) (δ := 7689/1000000000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t361 : ((19854812323/400000000000 : ℚ) : ℝ) ≤ stT301o2 361 := by
  have hc : ((188621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((361 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19854812323/400000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((188621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c362 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((362 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((145637/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29458221/10000000 : ℚ) : ℝ) ≤ Real.log ((362 : ℕ)) / 2 := by
    have h := (log_br_362).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((362 : ℕ)) / 2 ≤ ((58916443/20000000 : ℚ) : ℝ) := by
    have h := (log_br_362).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 235977/1250000) (δ := 3807/500000000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t362 : ((19134950919/500000000000 : ℚ) : ℝ) ≤ stT301o2 362 := by
  have hc : ((145627/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((362 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19134950919/500000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((145627/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c363 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((363 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((389879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14736007/5000000 : ℚ) : ℝ) ≤ Real.log ((363 : ℕ)) / 2 := by
    have h := (log_br_363).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((363 : ℕ)) / 2 ≤ ((58944029/20000000 : ℚ) : ℝ) := by
    have h := (log_br_363).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2925739/10000000) (δ := 7539/1000000000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t363 : ((204606818427/10000000000000 : ℚ) : ℝ) ≤ stT301o2 363 := by
  have hc : ((389829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((363 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204606818427/10000000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((389829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c364 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((364 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-3381/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29485769/10000000 : ℚ) : ℝ) ≤ Real.log ((364 : ℕ)) / 2 := by
    have h := (log_br_364).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((364 : ℕ)) / 2 ≤ ((58971539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_364).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3960803/10000000) (δ := 3807/500000000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t364 : ((-3557358541/5000000000000 : ℚ) : ℝ) ≤ stT301o2 364 := by
  have hc : ((-6787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((364 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3557358541/5000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-6787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c365 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((365 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-25851/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58998973/20000000 : ℚ) : ℝ) ≤ Real.log ((365 : ℕ)) / 2 := by
    have h := (log_br_365).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((365 : ℕ)) / 2 ≤ ((29499487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_365).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 998609/2000000) (δ := 479/62500000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t365 : ((-3383167381/156250000000 : ℚ) : ℝ) ≤ stT301o2 365 := by
  have hc : ((-206833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((365 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3383167381/156250000000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-206833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c366 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((366 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-371717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59026333/20000000 : ℚ) : ℝ) ≤ Real.log ((366 : ℕ)) / 2 := by
    have h := (log_br_366).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((366 : ℕ)) / 2 ≤ ((29513167/10000000 : ℚ) : ℝ) := by
    have h := (log_br_366).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1204493/2000000) (δ := 479/62500000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t366 : ((-97156444539/2500000000000 : ℚ) : ℝ) ≤ stT301o2 366 := by
  have hc : ((-185871/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((366 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97156444539/2500000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-185871/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c367 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((367 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-189723/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29526809/10000000 : ℚ) : ℝ) ≤ Real.log ((367 : ℕ)) / 2 := by
    have h := (log_br_367).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((367 : ℕ)) / 2 ≤ ((59053619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_367).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7049063/10000000) (δ := 3807/500000000) (ψ := 1641/200000) 301 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t367 : ((-24759966767/500000000000 : ℚ) : ℝ) ≤ stT301o2 367 := by
  have hc : ((-189733/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((367 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24759966767/500000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-189733/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c368 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((368 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-996169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59080829/20000000 : ℚ) : ℝ) ≤ Real.log ((368 : ℕ)) / 2 := by
    have h := (log_br_368).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((368 : ℕ)) / 2 ≤ ((5908083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_368).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7635087/10000000) (δ := 3841/500000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t368 : ((-519316013853/10000000000000 : ℚ) : ℝ) ≤ stT301o2 368 := by
  have hc : ((-996219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((368 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).2
  have h0 : (0:ℝ) ≤ ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-519316013853/10000000000000 : ℚ) : ℝ)
      = ((521287/10000000 : ℚ) : ℝ) * ((-996219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c369 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((369 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-219877/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29553983/10000000 : ℚ) : ℝ) ≤ Real.log ((369 : ℕ)) / 2 := by
    have h := (log_br_369).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((369 : ℕ)) / 2 ≤ ((59107967/20000000 : ℚ) : ℝ) := by
    have h := (log_br_369).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6614057/10000000) (δ := 1883/250000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t369 : ((-11447007591/250000000000 : ℚ) : ℝ) ≤ stT301o2 369 := by
  have hc : ((-439779/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((369 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).2
  have h0 : (0:ℝ) ≤ ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11447007591/250000000000 : ℚ) : ℝ)
      = ((26029/500000 : ℚ) : ℝ) * ((-439779/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c370 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((370 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-123807/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5913503/2000000 : ℚ) : ℝ) ≤ Real.log ((370 : ℕ)) / 2 := by
    have h := (log_br_370).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((370 : ℕ)) / 2 ≤ ((59135031/20000000 : ℚ) : ℝ) := by
    have h := (log_br_370).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2797887/5000000) (δ := 1883/250000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t370 : ((-16092371673/500000000000 : ℚ) : ℝ) ≤ stT301o2 370 := by
  have hc : ((-123817/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((370 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16092371673/500000000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-123817/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c371 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((371 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-5167/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2958101/1000000 : ℚ) : ℝ) ≤ Real.log ((371 : ℕ)) / 2 := by
    have h := (log_br_371).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((371 : ℕ)) / 2 ≤ ((59162021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_371).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -183211/400000) (δ := 7621/1000000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t371 : ((-6707741/500000000 : ℚ) : ℝ) ≤ stT301o2 371 := by
  have hc : ((-323/1250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((371 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6707741/500000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-323/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c372 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((372 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((143307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29594469/10000000 : ℚ) : ℝ) ≤ Real.log ((372 : ℕ)) / 2 := by
    have h := (log_br_372).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((372 : ℕ)) / 2 ≤ ((59188939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_372).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -713497/2000000) (δ := 7721/1000000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t372 : ((2971006923/400000000000 : ℚ) : ℝ) ≤ stT301o2 372 := by
  have hc : ((143257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((372 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2971006923/400000000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((143257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c373 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((373 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((13021/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7401973/2500000 : ℚ) : ℝ) ≤ Real.log ((373 : ℕ)) / 2 := by
    have h := (log_br_373).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((373 : ℕ)) / 2 ≤ ((11843157/4000000 : ℚ) : ℝ) := by
    have h := (log_br_373).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -511481/2000000) (δ := 477/62500000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t373 : ((1348273231/50000000000 : ℚ) : ℝ) ≤ stT301o2 373 := by
  have hc : ((52079/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((373 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1348273231/50000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((52079/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c374 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((374 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((406931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59242557/20000000 : ℚ) : ℝ) ≤ Real.log ((374 : ℕ)) / 2 := by
    have h := (log_br_374).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((374 : ℕ)) / 2 ≤ ((29621279/10000000 : ℚ) : ℝ) := by
    have h := (log_br_374).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1550071/10000000) (δ := 3841/500000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t374 : ((105202901411/2500000000000 : ℚ) : ℝ) ≤ stT301o2 374 := by
  have hc : ((203453/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((374 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).1
  have hw2 : ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((517087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105202901411/2500000000000 : ℚ) : ℝ)
      = ((517087/10000000 : ℚ) : ℝ) * ((203453/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c375 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((375 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((9763/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2963463/1000000 : ℚ) : ℝ) ≤ Real.log ((375 : ℕ)) / 2 := by
    have h := (log_br_375).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((375 : ℕ)) / 2 ≤ ((59269261/20000000 : ℚ) : ℝ) := by
    have h := (log_br_375).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -54537/1000000) (δ := 7621/1000000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t375 : ((403306057/8000000000 : ℚ) : ℝ) ≤ stT301o2 375 := by
  have hc : ((781/800 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((375 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((403306057/8000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((781/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c376 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((376 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((491683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59295891/20000000 : ℚ) : ℝ) ≤ Real.log ((376 : ℕ)) / 2 := by
    have h := (log_br_376).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((376 : ℕ)) / 2 ≤ ((14823973/5000000 : ℚ) : ℝ) := by
    have h := (log_br_376).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 456621/10000000) (δ := 3791/500000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t376 : ((12677647359/250000000000 : ℚ) : ℝ) ≤ stT301o2 376 := by
  have hc : ((245829/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((376 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12677647359/250000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((245829/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c377 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((377 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((417579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59322451/20000000 : ℚ) : ℝ) ≤ Real.log ((377 : ℕ)) / 2 := by
    have h := (log_br_377).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((377 : ℕ)) / 2 ≤ ((14830613/5000000 : ℚ) : ℝ) := by
    have h := (log_br_377).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1455941/10000000) (δ := 3791/500000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t377 : ((53762791601/1250000000000 : ℚ) : ℝ) ≤ stT301o2 377 := by
  have hc : ((208777/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((377 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53762791601/1250000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((208777/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c378 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((378 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((11123/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59348941/20000000 : ℚ) : ℝ) ≤ Real.log ((378 : ℕ)) / 2 := by
    have h := (log_br_378).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((378 : ℕ)) / 2 ≤ ((29674471/10000000 : ℚ) : ℝ) := by
    have h := (log_br_378).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2452627/10000000) (δ := 3841/500000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t378 : ((357533373/12500000000 : ℚ) : ℝ) ≤ stT301o2 378 := by
  have hc : ((5561/10000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((378 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((357533373/12500000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((5561/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c379 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((379 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((19093/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29687681/10000000 : ℚ) : ℝ) ≤ Real.log ((379 : ℕ)) / 2 := by
    have h := (log_br_379).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((379 : ℕ)) / 2 ≤ ((59375363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_379).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1723359/5000000) (δ := 7721/1000000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t379 : ((122560469/12500000000 : ℚ) : ℝ) ≤ stT301o2 379 := by
  have hc : ((1193/6250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((379 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122560469/12500000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((1193/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c380 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((380 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-203037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3712607/1250000 : ℚ) : ℝ) ≤ Real.log ((380 : ℕ)) / 2 := by
    have h := (log_br_380).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((380 : ℕ)) / 2 ≤ ((59401713/20000000 : ℚ) : ℝ) := by
    have h := (log_br_380).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 554767/1250000) (δ := 477/62500000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t380 : ((-10418160013/1000000000000 : ℚ) : ℝ) ≤ stT301o2 380 := by
  have hc : ((-203087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((380 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10418160013/1000000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-203087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c381 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((381 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-70579/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59427993/20000000 : ℚ) : ℝ) ≤ Real.log ((381 : ℕ)) / 2 := by
    have h := (log_br_381).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((381 : ℕ)) / 2 ≤ ((29713997/10000000 : ℚ) : ℝ) := by
    have h := (log_br_381).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5426959/10000000) (δ := 7571/1000000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t381 : ((-36161952939/1250000000000 : ℚ) : ℝ) ≤ stT301o2 381 := by
  have hc : ((-282341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((381 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36161952939/1250000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-282341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c382 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((382 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-838483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29727103/10000000 : ℚ) : ℝ) ≤ Real.log ((382 : ℕ)) / 2 := by
    have h := (log_br_382).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((382 : ℕ)) / 2 ≤ ((59454207/20000000 : ℚ) : ℝ) := by
    have h := (log_br_382).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6413223/10000000) (δ := 1883/250000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t382 : ((-85806243357/2000000000000 : ℚ) : ℝ) ≤ stT301o2 382 := by
  have hc : ((-838533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((382 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85806243357/2000000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-838533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c383 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((383 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-983329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59480349/20000000 : ℚ) : ℝ) ≤ Real.log ((383 : ℕ)) / 2 := by
    have h := (log_br_383).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((383 : ℕ)) / 2 ≤ ((1189607/400000 : ℚ) : ℝ) := by
    have h := (log_br_383).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7396853/10000000) (δ := 3841/500000000) (ψ := 1641/200000) 301 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t383 : ((-502484051283/10000000000000 : ℚ) : ℝ) ≤ stT301o2 383 := by
  have hc : ((-983379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((383 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).2
  have h0 : (0:ℝ) ≤ ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-502484051283/10000000000000 : ℚ) : ℝ)
      = ((510977/10000000 : ℚ) : ℝ) * ((-983379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c384 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((384 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-244529/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2380257/800000 : ℚ) : ℝ) ≤ Real.log ((384 : ℕ)) / 2 := by
    have h := (log_br_384).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((384 : ℕ)) / 2 ≤ ((29753213/10000000 : ℚ) : ℝ) := by
    have h := (log_br_384).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -733/1000) (δ := 3839/500000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t384 : ((-249584434813/5000000000000 : ℚ) : ℝ) ≤ stT301o2 384 := by
  have hc : ((-489083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((384 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249584434813/5000000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-489083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c385 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((385 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-824763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59532433/20000000 : ℚ) : ℝ) ≤ Real.log ((385 : ℕ)) / 2 := by
    have h := (log_br_385).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((385 : ℕ)) / 2 ≤ ((29766217/10000000 : ℚ) : ℝ) := by
    have h := (log_br_385).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6351449/10000000) (δ := 3839/500000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t385 : ((-26272768489/625000000000 : ℚ) : ℝ) ≤ stT301o2 385 := by
  have hc : ((-824813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((385 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26272768489/625000000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-824813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c386 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((386 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-547511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59558373/20000000 : ℚ) : ℝ) ≤ Real.log ((386 : ℕ)) / 2 := by
    have h := (log_br_386).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((386 : ℕ)) / 2 ≤ ((29779187/10000000 : ℚ) : ℝ) := by
    have h := (log_br_386).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5375457/10000000) (δ := 303/40000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t386 : ((-278701430707/10000000000000 : ℚ) : ℝ) ≤ stT301o2 386 := by
  have hc : ((-547561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((386 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278701430707/10000000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-547561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c387 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((387 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-188857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29792123/10000000 : ℚ) : ℝ) ≤ Real.log ((387 : ℕ)) / 2 := by
    have h := (log_br_387).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((387 : ℕ)) / 2 ≤ ((59584247/20000000 : ℚ) : ℝ) := by
    have h := (log_br_387).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -880397/2000000) (δ := 1907/250000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t387 : ((-96026906403/10000000000000 : ℚ) : ℝ) ≤ stT301o2 387 := by
  have hc : ((-188907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((387 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96026906403/10000000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-188907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c388 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((388 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((197099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59610053/20000000 : ℚ) : ℝ) ≤ Real.log ((388 : ℕ)) / 2 := by
    have h := (log_br_388).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((388 : ℕ)) / 2 ≤ ((29805027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_388).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3430997/10000000) (δ := 303/40000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t388 : ((100036456977/10000000000000 : ℚ) : ℝ) ≤ stT301o2 388 := by
  have hc : ((197049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((388 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100036456977/10000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((197049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c389 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((389 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((552853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59635793/20000000 : ℚ) : ℝ) ≤ Real.log ((389 : ℕ)) / 2 := by
    have h := (log_br_389).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((389 : ℕ)) / 2 ≤ ((29817897/10000000 : ℚ) : ℝ) := by
    have h := (log_br_389).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2462529/10000000) (δ := 3839/500000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t389 : ((14014108853/500000000000 : ℚ) : ℝ) ≤ stT301o2 389 := by
  have hc : ((552803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((389 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14014108853/500000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((552803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c390 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((390 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((165223/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59661467/20000000 : ℚ) : ℝ) ≤ Real.log ((390 : ℕ)) / 2 := by
    have h := (log_br_390).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((390 : ℕ)) / 2 ≤ ((14915367/5000000 : ℚ) : ℝ) := by
    have h := (log_br_390).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -299309/2000000) (δ := 3789/500000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t390 : ((83658741597/2000000000000 : ℚ) : ℝ) ≤ stT301o2 390 := by
  have hc : ((165213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((390 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83658741597/2000000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((165213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c391 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((391 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((195471/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2387483/800000 : ℚ) : ℝ) ≤ Real.log ((391 : ℕ)) / 2 := by
    have h := (log_br_391).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((391 : ℕ)) / 2 ≤ ((14921769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_391).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -133261/2500000) (δ := 3789/500000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t391 : ((98848732381/2000000000000 : ℚ) : ℝ) ≤ stT301o2 391 := by
  have hc : ((195461/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((391 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98848732381/2000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((195461/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c392 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((392 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((49269/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29856309/10000000 : ℚ) : ℝ) ≤ Real.log ((392 : ℕ)) / 2 := by
    have h := (log_br_392).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((392 : ℕ)) / 2 ≤ ((59712619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_392).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 428011/10000000) (δ := 61/8000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t392 : ((12441663377/250000000000 : ℚ) : ℝ) ≤ stT301o2 392 := by
  have hc : ((98533/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((392 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12441663377/250000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((98533/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c393 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((393 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((425043/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3733631/1250000 : ℚ) : ℝ) ≤ Real.log ((393 : ℕ)) / 2 := by
    have h := (log_br_393).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((393 : ℕ)) / 2 ≤ ((59738097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_393).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1386621/10000000) (δ := 941/125000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t393 : ((107196552397/2500000000000 : ℚ) : ℝ) ≤ stT301o2 393 := by
  have hc : ((212509/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((393 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107196552397/2500000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((212509/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c394 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((394 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((148029/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59763509/20000000 : ℚ) : ℝ) ≤ Real.log ((394 : ℕ)) / 2 := by
    have h := (log_br_394).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((394 : ℕ)) / 2 ≤ ((5976351/2000000 : ℚ) : ℝ) := by
    have h := (log_br_394).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 468557/2000000) (δ := 303/40000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t394 : ((9321191071/312500000000 : ℚ) : ℝ) ≤ stT301o2 394 := by
  have hc : ((296033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((394 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9321191071/312500000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((296033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c395 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((395 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((24953/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59788857/20000000 : ℚ) : ℝ) ≤ Real.log ((395 : ℕ)) / 2 := by
    have h := (log_br_395).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((395 : ℕ)) / 2 ≤ ((29894429/10000000 : ℚ) : ℝ) := by
    have h := (log_br_395).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 412063/1250000) (δ := 3839/500000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t395 : ((1569085749/125000000000 : ℚ) : ℝ) ≤ stT301o2 395 := by
  have hc : ((6237/25000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((395 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1569085749/125000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((6237/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c396 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((396 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-15999/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29907071/10000000 : ℚ) : ℝ) ≤ Real.log ((396 : ℕ)) / 2 := by
    have h := (log_br_396).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((396 : ℕ)) / 2 ≤ ((59814143/20000000 : ℚ) : ℝ) := by
    have h := (log_br_396).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1061963/2500000) (δ := 1907/250000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t396 : ((-32171768899/5000000000000 : ℚ) : ℝ) ≤ stT301o2 396 := by
  have hc : ((-64021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((396 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32171768899/5000000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-64021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c397 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((397 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-121587/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29919681/10000000 : ℚ) : ℝ) ≤ Real.log ((397 : ℕ)) / 2 := by
    have h := (log_br_397).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((397 : ℕ)) / 2 ≤ ((59839363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_397).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2598377/5000000) (δ := 61/8000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t397 : ((-61029086657/2500000000000 : ℚ) : ℝ) ≤ stT301o2 397 := by
  have hc : ((-243199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((397 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61029086657/2500000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-243199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c398 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((398 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-154977/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1496613/500000 : ℚ) : ℝ) ≤ Real.log ((398 : ℕ)) / 2 := by
    have h := (log_br_398).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((398 : ℕ)) / 2 ≤ ((59864521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_398).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1535831/2500000) (δ := 941/125000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t398 : ((-15537601737/400000000000 : ℚ) : ℝ) ≤ stT301o2 398 := by
  have hc : ((-154987/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((398 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15537601737/400000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-154987/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c399 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((399 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-476683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29944807/10000000 : ℚ) : ℝ) ≤ Real.log ((399 : ℕ)) / 2 := by
    have h := (log_br_399).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((399 : ℕ)) / 2 ≤ ((11977923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_399).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3543743/5000000) (δ := 1907/250000000) (ψ := 1641/200000) 301 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t399 : ((-59663223979/1250000000000 : ℚ) : ℝ) ≤ stT301o2 399 := by
  have hc : ((-119177/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((399 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59663223979/1250000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-119177/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c400 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((400 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-997543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11982929/4000000 : ℚ) : ℝ) ≤ Real.log ((400 : ℕ)) / 2 := by
    have h := (log_br_400).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((400 : ℕ)) / 2 ≤ ((29957323/10000000 : ℚ) : ℝ) := by
    have h := (log_br_400).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3839343/5000000) (δ := 1517/200000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t400 : ((-498797497593/10000000000000 : ℚ) : ℝ) ≤ stT301o2 400 := by
  have hc : ((-997593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((400 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-498797497593/10000000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-997593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c401 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((401 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-451111/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29969807/10000000 : ℚ) : ℝ) ≤ Real.log ((401 : ℕ)) / 2 := by
    have h := (log_br_401).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((401 : ℕ)) / 2 ≤ ((11987923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_401).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1684807/2500000) (δ := 3859/500000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t401 : ((-3520108473/78125000000 : ℚ) : ℝ) ≤ stT301o2 401 := by
  have hc : ((-14098/15625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((401 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3520108473/78125000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-14098/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c402 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((402 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-340841/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1499113/500000 : ℚ) : ℝ) ≤ Real.log ((402 : ℕ)) / 2 := by
    have h := (log_br_402).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((402 : ℕ)) / 2 ≤ ((59964521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_402).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5802139/10000000) (δ := 1527/200000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t402 : ((-17000862183/500000000000 : ℚ) : ℝ) ≤ stT301o2 402 := by
  have hc : ((-170433/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((402 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17000862183/500000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-170433/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c403 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((403 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-73467/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11997873/4000000 : ℚ) : ℝ) ≤ Real.log ((403 : ℕ)) / 2 := by
    have h := (log_br_403).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((403 : ℕ)) / 2 ≤ ((29994683/10000000 : ℚ) : ℝ) := by
    have h := (log_br_403).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2433673/5000000) (δ := 1517/200000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t403 : ((-4575192359/250000000000 : ℚ) : ℝ) ≤ stT301o2 403 := by
  have hc : ((-73477/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((403 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4575192359/250000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-73477/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c404 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((404 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-1579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15003537/5000000 : ℚ) : ℝ) ≤ Real.log ((404 : ℕ)) / 2 := by
    have h := (log_br_404).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((404 : ℕ)) / 2 ≤ ((60014149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_404).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1967443/5000000) (δ := 3809/500000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t404 : ((-199505119/1250000000000 : ℚ) : ℝ) ≤ stT301o2 404 := by
  have hc : ((-401/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((404 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199505119/1250000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-401/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c405 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((405 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((360597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6003887/2000000 : ℚ) : ℝ) ≤ Real.log ((405 : ℕ)) / 2 := by
    have h := (log_br_405).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((405 : ℕ)) / 2 ≤ ((60038871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_405).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3004721/10000000) (δ := 3859/500000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t405 : ((179156885941/10000000000000 : ℚ) : ℝ) ≤ stT301o2 405 := by
  have hc : ((360547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((405 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179156885941/10000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((360547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c406 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((406 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((67433/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60063531/20000000 : ℚ) : ℝ) ≤ Real.log ((406 : ℕ)) / 2 := by
    have h := (log_br_406).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((406 : ℕ)) / 2 ≤ ((15015883/5000000 : ℚ) : ℝ) := by
    have h := (log_br_406).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -41537/200000) (δ := 1537/200000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t406 : ((8365977387/250000000000 : ℚ) : ℝ) ≤ stT301o2 406 := by
  have hc : ((16857/25000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((406 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8365977387/250000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((16857/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c407 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((407 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((447913/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60088131/20000000 : ℚ) : ℝ) ≤ Real.log ((407 : ℕ)) / 2 := by
    have h := (log_br_407).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((407 : ℕ)) / 2 ≤ ((15022033/5000000 : ℚ) : ℝ) := by
    have h := (log_br_407).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -46051/400000) (δ := 1537/200000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t407 : ((13875598233/312500000000 : ℚ) : ℝ) ≤ stT301o2 407 := by
  have hc : ((27993/31250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((407 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13875598233/312500000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((27993/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c408 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((408 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((497923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60112671/20000000 : ℚ) : ℝ) ≤ Real.log ((408 : ℕ)) / 2 := by
    have h := (log_br_408).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((408 : ℕ)) / 2 ≤ ((1878521/625000 : ℚ) : ℝ) := by
    have h := (log_br_408).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -113979/5000000) (δ := 473/62500000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t408 : ((123247928277/2500000000000 : ℚ) : ℝ) ≤ stT301o2 408 := by
  have hc : ((248949/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((408 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123247928277/2500000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((248949/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c409 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((409 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((480907/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60137151/20000000 : ℚ) : ℝ) ≤ Real.log ((409 : ℕ)) / 2 := by
    have h := (log_br_409).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((409 : ℕ)) / 2 ≤ ((939643/312500 : ℚ) : ℝ) := by
    have h := (log_br_409).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 346551/5000000) (δ := 473/62500000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t409 : ((29722595097/625000000000 : ℚ) : ℝ) ≤ stT301o2 409 := by
  have hc : ((240441/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((409 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29722595097/625000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((240441/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c410 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((410 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((799243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60161571/20000000 : ℚ) : ℝ) ≤ Real.log ((410 : ℕ)) / 2 := by
    have h := (log_br_410).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((410 : ℕ)) / 2 ≤ ((15040393/5000000 : ℚ) : ℝ) := by
    have h := (log_br_410).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 322381/2000000) (δ := 1537/200000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t410 : ((49336581469/1250000000000 : ℚ) : ℝ) ≤ stT301o2 410 := by
  have hc : ((799193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((410 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49336581469/1250000000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((799193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c411 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((411 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((530679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15046483/5000000 : ℚ) : ℝ) ≤ Real.log ((411 : ℕ)) / 2 := by
    have h := (log_br_411).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((411 : ℕ)) / 2 ≤ ((60185933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_411).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2528487/10000000) (δ := 3809/500000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t411 : ((261739652427/10000000000000 : ℚ) : ℝ) ≤ stT301o2 411 := by
  have hc : ((530629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((411 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261739652427/10000000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((530629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c412 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((412 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((192463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60210233/20000000 : ℚ) : ℝ) ≤ Real.log ((412 : ℕ)) / 2 := by
    have h := (log_br_412).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((412 : ℕ)) / 2 ≤ ((30105117/10000000 : ℚ) : ℝ) := by
    have h := (log_br_412).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 860703/2500000) (δ := 1917/250000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t412 : ((11849369779/1250000000000 : ℚ) : ℝ) ≤ stT301o2 412 := by
  have hc : ((192413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((412 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11849369779/1250000000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((192413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c413 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((413 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-5323/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2409379/800000 : ℚ) : ℝ) ≤ Real.log ((413 : ℕ)) / 2 := by
    have h := (log_br_413).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((413 : ℕ)) / 2 ≤ ((15058619/5000000 : ℚ) : ℝ) := by
    have h := (log_br_413).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2177459/5000000) (δ := 1537/200000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t413 : ((-10480187281/1250000000000 : ℚ) : ℝ) ≤ stT301o2 413 := by
  have hc : ((-85193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((413 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10480187281/1250000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-85193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c414 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((414 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-254981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60258659/20000000 : ℚ) : ℝ) ≤ Real.log ((414 : ℕ)) / 2 := by
    have h := (log_br_414).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((414 : ℕ)) / 2 ≤ ((3012933/1000000 : ℚ) : ℝ) := by
    have h := (log_br_414).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5264841/10000000) (δ := 1537/200000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t414 : ((-31332204711/1250000000000 : ℚ) : ℝ) ≤ stT301o2 414 := by
  have hc : ((-127503/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((414 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31332204711/1250000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-127503/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c415 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((415 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-782229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12056557/4000000 : ℚ) : ℝ) ≤ Real.log ((415 : ℕ)) / 2 := by
    have h := (log_br_415).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((415 : ℕ)) / 2 ≤ ((30141393/10000000 : ℚ) : ℝ) := by
    have h := (log_br_415).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6172581/10000000) (δ := 1917/250000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t415 : ((-384005897799/10000000000000 : ℚ) : ℝ) ≤ stT301o2 415 := by
  have hc : ((-782279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((415 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-384005897799/10000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-782279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c416 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((416 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-476113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15076713/5000000 : ℚ) : ℝ) ≤ Real.log ((416 : ℕ)) / 2 := by
    have h := (log_br_416).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((416 : ℕ)) / 2 ≤ ((60306853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_416).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3539051/5000000) (δ := 3809/500000000) (ψ := 1641/200000) 301 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t416 : ((-116723088079/2500000000000 : ℚ) : ℝ) ≤ stT301o2 416 := by
  have hc : ((-238069/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((416 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116723088079/2500000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-238069/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c417 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((417 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-9987/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30165431/10000000 : ℚ) : ℝ) ≤ Real.log ((417 : ℕ)) / 2 := by
    have h := (log_br_417).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((417 : ℕ)) / 2 ≤ ((60330863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_417).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1545297/2000000) (δ := 761/100000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t417 : ((-391272697/8000000000 : ℚ) : ℝ) ≤ stT301o2 417 := by
  have hc : ((-799/800 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((417 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-391272697/8000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-799/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c418 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((418 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-916531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30177407/10000000 : ℚ) : ℝ) ≤ Real.log ((418 : ℕ)) / 2 := by
    have h := (log_br_418).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((418 : ℕ)) / 2 ≤ ((12070963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_418).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6825291/10000000) (δ := 761/100000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t418 : ((-112078608099/2500000000000 : ℚ) : ℝ) ≤ stT301o2 418 := by
  have hc : ((-916581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((418 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112078608099/2500000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-916581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c419 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((419 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-717147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60378709/20000000 : ℚ) : ℝ) ≤ Real.log ((419 : ℕ)) / 2 := by
    have h := (log_br_419).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((419 : ℕ)) / 2 ≤ ((6037871/2000000 : ℚ) : ℝ) := by
    have h := (log_br_419).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5926241/10000000) (δ := 7693/1000000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t419 : ((-87593421201/2500000000000 : ℚ) : ℝ) ≤ stT301o2 419 := by
  have hc : ((-717197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((419 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87593421201/2500000000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-717197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c420 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((420 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-106697/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60402547/20000000 : ℚ) : ℝ) ≤ Real.log ((420 : ℕ)) / 2 := by
    have h := (log_br_420).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((420 : ℕ)) / 2 ≤ ((15100637/5000000 : ℚ) : ℝ) := by
    have h := (log_br_420).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5029337/10000000) (δ := 383/50000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t420 : ((-104138014469/5000000000000 : ℚ) : ℝ) ≤ stT301o2 420 := by
  have hc : ((-213419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((420 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).2
  have h0 : (0:ℝ) ≤ ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104138014469/5000000000000 : ℚ) : ℝ)
      = ((487951/10000000 : ℚ) : ℝ) * ((-213419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c421 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((421 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-82939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7553291/2500000 : ℚ) : ℝ) ≤ Real.log ((421 : ℕ)) / 2 := by
    have h := (log_br_421).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((421 : ℕ)) / 2 ≤ ((60426329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_421).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4134577/10000000) (δ := 771/100000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t421 : ((-40446431919/10000000000000 : ℚ) : ℝ) ≤ stT301o2 421 := by
  have hc : ((-82989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((421 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).2
  have h0 : (0:ℝ) ≤ ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40446431919/10000000000000 : ℚ) : ℝ)
      = ((487371/10000000 : ℚ) : ℝ) * ((-82989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c422 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((422 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((27061/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60450053/20000000 : ℚ) : ℝ) ≤ Real.log ((422 : ℕ)) / 2 := by
    have h := (log_br_422).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((422 : ℕ)) / 2 ≤ ((30225027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_422).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3241923/10000000) (δ := 7693/1000000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t422 : ((102895659/7812500000 : ℚ) : ℝ) ≤ stT301o2 422 := by
  have hc : ((1691/6250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((422 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102895659/7812500000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((1691/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c423 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((423 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((589331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60473721/20000000 : ℚ) : ℝ) ≤ Real.log ((423 : ℕ)) / 2 := by
    have h := (log_br_423).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((423 : ℕ)) / 2 ≤ ((30236861/10000000 : ℚ) : ℝ) := by
    have h := (log_br_423).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -470283/2000000) (δ := 189/25000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t423 : ((35814731337/1250000000000 : ℚ) : ℝ) ≤ stT301o2 423 := by
  have hc : ((589281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((423 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35814731337/1250000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((589281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c424 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((424 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((833607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30248667/10000000 : ℚ) : ℝ) ≤ Real.log ((424 : ℕ)) / 2 := by
    have h := (log_br_424).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((424 : ℕ)) / 2 ≤ ((12099467/4000000 : ℚ) : ℝ) := by
    have h := (log_br_424).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -22859/156250) (δ := 761/100000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t424 : ((202405144297/5000000000000 : ℚ) : ℝ) ≤ stT301o2 424 := by
  have hc : ((833557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((424 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202405144297/5000000000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((833557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c425 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((425 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((243379/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60520891/20000000 : ℚ) : ℝ) ≤ Real.log ((425 : ℕ)) / 2 := by
    have h := (log_br_425).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((425 : ℕ)) / 2 ≤ ((15130223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_425).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -144161/2500000) (δ := 383/50000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t425 : ((236100063043/5000000000000 : ℚ) : ℝ) ≤ stT301o2 425 := by
  have hc : ((486733/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((425 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).1
  have hw2 : ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((485071/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236100063043/5000000000000 : ℚ) : ℝ)
      = ((485071/10000000 : ℚ) : ℝ) * ((486733/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c426 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((426 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((992439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60544393/20000000 : ℚ) : ℝ) ≤ Real.log ((426 : ℕ)) / 2 := by
    have h := (log_br_426).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((426 : ℕ)) / 2 ≤ ((30272197/10000000 : ℚ) : ℝ) := by
    have h := (log_br_426).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 307619/10000000) (δ := 189/25000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t426 : ((480813462889/10000000000000 : ℚ) : ℝ) ≤ stT301o2 426 := by
  have hc : ((992389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((426 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).1
  have hw2 : ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((484501/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((480813462889/10000000000000 : ℚ) : ℝ)
      = ((484501/10000000 : ℚ) : ℝ) * ((992389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c427 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((427 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((888869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((378549/125000 : ℚ) : ℝ) ≤ Real.log ((427 : ℕ)) / 2 := by
    have h := (log_br_427).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((427 : ℕ)) / 2 ≤ ((60567841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_427).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 297453/2500000) (δ := 771/100000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t427 : ((430128845127/10000000000000 : ℚ) : ℝ) ≤ stT301o2 427 := by
  have hc : ((888819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((427 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).1
  have hw2 : ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((483933/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((430128845127/10000000000000 : ℚ) : ℝ)
      = ((483933/10000000 : ℚ) : ℝ) * ((888819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c428 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((428 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((33819/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60591231/20000000 : ℚ) : ℝ) ≤ Real.log ((428 : ℕ)) / 2 := by
    have h := (log_br_428).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((428 : ℕ)) / 2 ≤ ((473369/156250 : ℚ) : ℝ) := by
    have h := (log_br_428).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2069899/10000000) (δ := 7593/1000000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t428 : ((4086453493/125000000000 : ℚ) : ℝ) ≤ stT301o2 428 := by
  have hc : ((67633/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((428 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).1
  have hw2 : ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4086453493/125000000000 : ℚ) : ℝ)
      = ((60421/1250000 : ℚ) : ℝ) * ((67633/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c429 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((429 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((95417/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60614569/20000000 : ℚ) : ℝ) ≤ Real.log ((429 : ℕ)) / 2 := by
    have h := (log_br_429).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((429 : ℕ)) / 2 ≤ ((6061457/2000000 : ℚ) : ℝ) := by
    have h := (log_br_429).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2947991/10000000) (δ := 189/25000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t429 : ((23030837109/1250000000000 : ℚ) : ℝ) ≤ stT301o2 429 := by
  have hc : ((190809/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((429 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).1
  have hw2 : ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((120701/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23030837109/1250000000000 : ℚ) : ℝ)
      = ((120701/2500000 : ℚ) : ℝ) * ((190809/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c430 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((430 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((41179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15159463/5000000 : ℚ) : ℝ) ≤ Real.log ((430 : ℕ)) / 2 := by
    have h := (log_br_430).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((430 : ℕ)) / 2 ≤ ((60637853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_430).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1912007/5000000) (δ := 7543/1000000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t430 : ((9917065609/5000000000000 : ℚ) : ℝ) ≤ stT301o2 430 := by
  have hc : ((41129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((430 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).1
  have hw2 : ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((241121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9917065609/5000000000000 : ℚ) : ℝ)
      = ((241121/5000000 : ℚ) : ℝ) * ((41129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c431 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((431 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-12141/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1516527/500000 : ℚ) : ℝ) ≤ Real.log ((431 : ℕ)) / 2 := by
    have h := (log_br_431).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((431 : ℕ)) / 2 ≤ ((60661081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_431).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4697967/10000000) (δ := 771/100000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t431 : ((-1462272203/100000000000 : ℚ) : ℝ) ≤ stT301o2 431 := by
  have hc : ((-12143/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((431 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).2
  have h0 : (0:ℝ) ≤ ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1462272203/100000000000 : ℚ) : ℝ)
      = ((120421/2500000 : ℚ) : ℝ) * ((-12143/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c432 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((432 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-305441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12136851/4000000 : ℚ) : ℝ) ≤ Real.log ((432 : ℕ)) / 2 := by
    have h := (log_br_432).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((432 : ℕ)) / 2 ≤ ((1896383/625000 : ℚ) : ℝ) := by
    have h := (log_br_432).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5569927/10000000) (δ := 7593/1000000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t432 : ((-36741908679/1250000000000 : ℚ) : ℝ) ≤ stT301o2 432 := by
  have hc : ((-152733/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((432 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).2
  have h0 : (0:ℝ) ≤ ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36741908679/1250000000000 : ℚ) : ℝ)
      = ((240563/5000000 : ℚ) : ℝ) * ((-152733/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c433 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((433 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-105531/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60707377/20000000 : ℚ) : ℝ) ≤ Real.log ((433 : ℕ)) / 2 := by
    have h := (log_br_433).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((433 : ℕ)) / 2 ≤ ((30353689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_433).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1609973/2500000) (δ := 189/25000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t433 : ((-20287214493/500000000000 : ℚ) : ℝ) ≤ stT301o2 433 := by
  have hc : ((-422149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((433 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).2
  have h0 : (0:ℝ) ≤ ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20287214493/500000000000 : ℚ) : ℝ)
      = ((48057/1000000 : ℚ) : ℝ) * ((-422149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c434 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((434 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-122029/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12146089/4000000 : ℚ) : ℝ) ≤ Real.log ((434 : ℕ)) / 2 := by
    have h := (log_br_434).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((434 : ℕ)) / 2 ≤ ((30365223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_434).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3653913/5000000) (δ := 7693/1000000000) (ψ := 1641/200000) 301 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t434 : ((-14644718141/312500000000 : ℚ) : ℝ) ≤ stT301o2 434 := by
  have hc : ((-488141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((434 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).2
  have h0 : (0:ℝ) ≤ ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14644718141/312500000000 : ℚ) : ℝ)
      = ((30001/625000 : ℚ) : ℝ) * ((-488141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c435 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((435 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-99183/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3037673/1000000 : ℚ) : ℝ) ≤ Real.log ((435 : ℕ)) / 2 := by
    have h := (log_br_435).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((435 : ℕ)) / 2 ≤ ((60753461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_435).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3767099/5000000) (δ := 153/20000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t435 : ((-1486158601/31250000000 : ℚ) : ℝ) ≤ stT301o2 435 := by
  have hc : ((-24797/25000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((435 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).2
  have h0 : (0:ℝ) ≤ ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1486158601/31250000000 : ℚ) : ℝ)
      = ((59933/1250000 : ℚ) : ℝ) * ((-24797/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c436 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((436 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-444991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30388211/10000000 : ℚ) : ℝ) ≤ Real.log ((436 : ℕ)) / 2 := by
    have h := (log_br_436).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((436 : ℕ)) / 2 ≤ ((60776423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_436).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6670253/10000000) (δ := 151/20000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t436 : ((-13320274539/312500000000 : ℚ) : ℝ) ≤ stT301o2 436 := by
  have hc : ((-55627/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((436 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).2
  have h0 : (0:ℝ) ≤ ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13320274539/312500000000 : ℚ) : ℝ)
      = ((239457/5000000 : ℚ) : ℝ) * ((-55627/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c437 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((437 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-170871/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60799331/20000000 : ℚ) : ℝ) ≤ Real.log ((437 : ℕ)) / 2 := by
    have h := (log_br_437).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((437 : ℕ)) / 2 ≤ ((15199833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_437).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2904151/5000000) (δ := 7553/1000000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t437 : ((-32697874191/1000000000000 : ℚ) : ℝ) ≤ stT301o2 437 := by
  have hc : ((-341767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((437 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32697874191/1000000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-341767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c438 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((438 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-99311/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60822189/20000000 : ℚ) : ℝ) ≤ Real.log ((438 : ℕ)) / 2 := by
    have h := (log_br_438).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((438 : ℕ)) / 2 ≤ ((6082219/2000000 : ℚ) : ℝ) := by
    have h := (log_br_438).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -494827/1000000) (δ := 7653/1000000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t438 : ((-94917310893/5000000000000 : ℚ) : ℝ) ≤ stT301o2 438 := by
  have hc : ((-198647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((438 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94917310893/5000000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-198647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c439 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((439 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-261/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30422497/10000000 : ℚ) : ℝ) ≤ Real.log ((439 : ℕ)) / 2 := by
    have h := (log_br_439).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((439 : ℕ)) / 2 ≤ ((12168999/4000000 : ℚ) : ℝ) := by
    have h := (log_br_439).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -511279/1250000) (δ := 7703/1000000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t439 : ((-155829961/50000000000 : ℚ) : ℝ) ≤ stT301o2 439 := by
  have hc : ((-653/10000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((439 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155829961/50000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-653/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c440 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((440 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((136801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60867747/20000000 : ℚ) : ℝ) ≤ Real.log ((440 : ℕ)) / 2 := by
    have h := (log_br_440).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((440 : ℕ)) / 2 ≤ ((15216937/5000000 : ℚ) : ℝ) := by
    have h := (log_br_440).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -64683/200000) (δ := 7553/1000000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t440 : ((8150669907/625000000000 : ℚ) : ℝ) ≤ stT301o2 440 := by
  have hc : ((17097/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((440 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).1
  have hw2 : ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8150669907/625000000000 : ℚ) : ℝ)
      = ((476731/10000000 : ℚ) : ℝ) * ((17097/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c441 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((441 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((580047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3805653/1250000 : ℚ) : ℝ) ≤ Real.log ((441 : ℕ)) / 2 := by
    have h := (log_br_441).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((441 : ℕ)) / 2 ≤ ((60890449/20000000 : ℚ) : ℝ) := by
    have h := (log_br_441).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -95201/400000) (δ := 7603/1000000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t441 : ((27618877143/1000000000000 : ℚ) : ℝ) ≤ stT301o2 441 := by
  have hc : ((579997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((441 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).1
  have hw2 : ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((47619/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27618877143/1000000000000 : ℚ) : ℝ)
      = ((47619/1000000 : ℚ) : ℝ) * ((579997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c442 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((442 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((409501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30456549/10000000 : ℚ) : ℝ) ≤ Real.log ((442 : ℕ)) / 2 := by
    have h := (log_br_442).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((442 : ℕ)) / 2 ≤ ((60913099/20000000 : ℚ) : ℝ) := by
    have h := (log_br_442).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1527819/10000000) (δ := 7703/1000000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t442 : ((48691917219/1250000000000 : ℚ) : ℝ) ≤ stT301o2 442 := by
  have hc : ((102369/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((442 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).1
  have hw2 : ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((475651/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48691917219/1250000000000 : ℚ) : ℝ)
      = ((475651/10000000 : ℚ) : ℝ) * ((102369/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c443 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((443 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((1927/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60935697/20000000 : ℚ) : ℝ) ≤ Real.log ((443 : ℕ)) / 2 := by
    have h := (log_br_443).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((443 : ℕ)) / 2 ≤ ((30467849/10000000 : ℚ) : ℝ) := by
    have h := (log_br_443).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -677531/10000000) (δ := 19/2500000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t443 : ((4577485833/100000000000 : ℚ) : ℝ) ≤ stT301o2 443 := by
  have hc : ((19269/20000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((443 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4577485833/100000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((19269/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c444 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((444 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((498833/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12191649/4000000 : ℚ) : ℝ) ≤ Real.log ((444 : ℕ)) / 2 := by
    have h := (log_br_444).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((444 : ℕ)) / 2 ≤ ((30479123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_444).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 170837/10000000) (δ := 7653/1000000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t444 : ((14795206439/312500000000 : ℚ) : ℝ) ≤ stT301o2 444 := by
  have hc : ((62351/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((444 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14795206439/312500000000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((62351/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c445 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((445 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((459173/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30490371/10000000 : ℚ) : ℝ) ≤ Real.log ((445 : ℕ)) / 2 := by
    have h := (log_br_445).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((445 : ℕ)) / 2 ≤ ((60980743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_445).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1017287/10000000) (δ := 151/20000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t445 : ((10882840683/250000000000 : ℚ) : ℝ) ≤ stT301o2 445 := by
  have hc : ((114787/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((445 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10882840683/250000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((114787/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c446 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((446 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((735263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61003189/20000000 : ℚ) : ℝ) ≤ Real.log ((446 : ℕ)) / 2 := by
    have h := (log_br_446).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((446 : ℕ)) / 2 ≤ ((6100319/2000000 : ℚ) : ℝ) := by
    have h := (log_br_446).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 372371/2000000) (δ := 7653/1000000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t446 : ((348132913269/10000000000000 : ℚ) : ℝ) ≤ stT301o2 446 := by
  have hc : ((735213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((446 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348132913269/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((735213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c447 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((447 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((234869/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12205117/4000000 : ℚ) : ℝ) ≤ Real.log ((447 : ℕ)) / 2 := by
    have h := (log_br_447).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((447 : ℕ)) / 2 ≤ ((30512793/10000000 : ℚ) : ℝ) := by
    have h := (log_br_447).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 540901/2000000) (δ := 19/2500000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t447 : ((27769304913/1250000000000 : ℚ) : ℝ) ≤ stT301o2 447 := by
  have hc : ((58711/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((447 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27769304913/1250000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((58711/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c448 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((448 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((1901/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15261983/5000000 : ℚ) : ℝ) ≤ Real.log ((448 : ℕ)) / 2 := by
    have h := (log_br_448).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((448 : ℕ)) / 2 ≤ ((61047933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_448).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3545311/10000000) (δ := 153/20000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t448 : ((1436546673/200000000000 : ℚ) : ℝ) ≤ stT301o2 448 := by
  have hc : ((15203/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((448 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1436546673/200000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((15203/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c449 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((449 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-36373/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15267557/5000000 : ℚ) : ℝ) ≤ Real.log ((449 : ℕ)) / 2 := by
    have h := (log_br_449).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((449 : ℕ)) / 2 ≤ ((61070229/20000000 : ℚ) : ℝ) := by
    have h := (log_br_449).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2192099/5000000) (δ := 153/20000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t449 : ((-1717022919/200000000000 : ℚ) : ℝ) ≤ stT301o2 449 := by
  have hc : ((-36383/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((449 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).2
  have h0 : (0:ℝ) ≤ ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1717022919/200000000000 : ℚ) : ℝ)
      = ((47193/1000000 : ℚ) : ℝ) * ((-36383/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c450 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((450 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-494883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2443699/800000 : ℚ) : ℝ) ≤ Real.log ((450 : ℕ)) / 2 := by
    have h := (log_br_450).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((450 : ℕ)) / 2 ≤ ((15273119/5000000 : ℚ) : ℝ) := by
    have h := (log_br_450).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5221241/10000000) (δ := 7553/1000000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t450 : ((-46662778173/2000000000000 : ℚ) : ℝ) ≤ stT301o2 450 := by
  have hc : ((-494933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((450 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46662778173/2000000000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-494933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c451 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((451 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-376227/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61114673/20000000 : ℚ) : ℝ) ≤ Real.log ((451 : ℕ)) / 2 := by
    have h := (log_br_451).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((451 : ℕ)) / 2 ≤ ((30557337/10000000 : ℚ) : ℝ) := by
    have h := (log_br_451).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6056441/10000000) (δ := 19/2500000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t451 : ((-22146286783/625000000000 : ℚ) : ℝ) ≤ stT301o2 451 := by
  have hc : ((-94063/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((451 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22146286783/625000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-94063/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c452 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((452 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-926539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61136821/20000000 : ℚ) : ℝ) ≤ Real.log ((452 : ℕ)) / 2 := by
    have h := (log_br_452).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((452 : ℕ)) / 2 ≤ ((30568411/10000000 : ℚ) : ℝ) := by
    have h := (log_br_452).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6889759/10000000) (δ := 7653/1000000000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t452 : ((-435831328629/10000000000000 : ℚ) : ℝ) ≤ stT301o2 452 := by
  have hc : ((-926589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((452 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-435831328629/10000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-926589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c453 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((453 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-998591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61158921/20000000 : ℚ) : ℝ) ≤ Real.log ((453 : ℕ)) / 2 := by
    have h := (log_br_453).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((453 : ℕ)) / 2 ≤ ((30579461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_453).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 965159/1250000) (δ := 19/2500000) (ψ := 1641/200000) 301 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t453 : ((-469202486081/10000000000000 : ℚ) : ℝ) ≤ stT301o2 453 := by
  have hc : ((-998641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((453 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-469202486081/10000000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-998641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c454 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((454 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-192279/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61180971/20000000 : ℚ) : ℝ) ≤ Real.log ((454 : ℕ)) / 2 := by
    have h := (log_br_454).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((454 : ℕ)) / 2 ≤ ((15295243/5000000 : ℚ) : ℝ) := by
    have h := (log_br_454).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -357853/500000) (δ := 7607/1000000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t454 : ((-22561460659/500000000000 : ℚ) : ℝ) ≤ stT301o2 454 := by
  have hc : ((-192289/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((454 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22561460659/500000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-192289/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c455 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((455 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-819697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30601487/10000000 : ℚ) : ℝ) ≤ Real.log ((455 : ℕ)) / 2 := by
    have h := (log_br_455).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((455 : ℕ)) / 2 ≤ ((2448119/800000 : ℚ) : ℝ) := by
    have h := (log_br_455).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6329197/10000000) (δ := 7657/1000000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t455 : ((-48037993947/1250000000000 : ℚ) : ℝ) ≤ stT301o2 455 := by
  have hc : ((-819747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((455 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48037993947/1250000000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-819747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c456 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((456 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-73691/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1913279/625000 : ℚ) : ℝ) ≤ Real.log ((456 : ℕ)) / 2 := by
    have h := (log_br_456).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((456 : ℕ)) / 2 ≤ ((61224929/20000000 : ℚ) : ℝ) := by
    have h := (log_br_456).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2751589/5000000) (δ := 7557/1000000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t456 : ((-138047625177/5000000000000 : ℚ) : ℝ) ≤ stT301o2 456 := by
  have hc : ((-294789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((456 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138047625177/5000000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-294789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c457 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((457 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-296289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61246833/20000000 : ℚ) : ℝ) ≤ Real.log ((457 : ℕ)) / 2 := by
    have h := (log_br_457).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((457 : ℕ)) / 2 ≤ ((30623417/10000000 : ℚ) : ℝ) := by
    have h := (log_br_457).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2339501/5000000) (δ := 7707/1000000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t457 : ((-138621753759/10000000000000 : ℚ) : ℝ) ≤ stT301o2 457 := by
  have hc : ((-296339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((457 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138621753759/10000000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-296339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c458 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((458 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((5631/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61268691/20000000 : ℚ) : ℝ) ≤ Real.log ((458 : ℕ)) / 2 := by
    have h := (log_br_458).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((458 : ℕ)) / 2 ≤ ((15317173/5000000 : ℚ) : ℝ) := by
    have h := (log_br_458).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -771319/2000000) (δ := 7607/1000000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t458 : ((2626519049/2000000000000 : ℚ) : ℝ) ≤ stT301o2 458 := by
  have hc : ((5621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((458 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2626519049/2000000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((5621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c459 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((459 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((87229/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30645251/10000000 : ℚ) : ℝ) ≤ Real.log ((459 : ℕ)) / 2 := by
    have h := (log_br_459).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((459 : ℕ)) / 2 ≤ ((61290503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_459).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -758989/2500000) (δ := 7657/1000000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t459 : ((2035458677/125000000000 : ℚ) : ℝ) ≤ stT301o2 459 := by
  have hc : ((174433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((459 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2035458677/125000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((174433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c460 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((460 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((315923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7664033/2500000 : ℚ) : ℝ) ≤ Real.log ((460 : ℕ)) / 2 := by
    have h := (log_br_460).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((460 : ℕ)) / 2 ≤ ((12262453/4000000 : ℚ) : ℝ) := by
    have h := (log_br_460).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2217161/10000000) (δ := 7557/1000000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t460 : ((18411009287/625000000000 : ℚ) : ℝ) ≤ stT301o2 460 := by
  have hc : ((157949/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((460 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18411009287/625000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((157949/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c461 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((461 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((169447/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3066699/1000000 : ℚ) : ℝ) ≤ Real.log ((461 : ℕ)) / 2 := by
    have h := (log_br_461).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((461 : ℕ)) / 2 ≤ ((61333981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_461).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1400097/10000000) (δ := 481/62500000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t461 : ((39457302501/1000000000000 : ℚ) : ℝ) ≤ stT301o2 461 := by
  have hc : ((169437/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((461 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39457302501/1000000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((169437/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c462 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((462 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((486381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((479341/156250 : ℚ) : ℝ) ≤ Real.log ((462 : ℕ)) / 2 := by
    have h := (log_br_462).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((462 : ℕ)) / 2 ≤ ((61355649/20000000 : ℚ) : ℝ) := by
    have h := (log_br_462).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -292419/5000000) (δ := 7557/1000000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t462 : ((28284154769/625000000000 : ℚ) : ℝ) ≤ stT301o2 462 := by
  have hc : ((121589/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((462 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28284154769/625000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((121589/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c463 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((463 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((995819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6137727/2000000 : ℚ) : ℝ) ≤ Real.log ((463 : ℕ)) / 2 := by
    have h := (log_br_463).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((463 : ℕ)) / 2 ≤ ((61377271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_463).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 22869/1000000) (δ := 7657/1000000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t463 : ((462772689291/10000000000000 : ℚ) : ℝ) ≤ stT301o2 463 := by
  have hc : ((995769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((463 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((462772689291/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((995769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c464 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((464 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((11433/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12279769/4000000 : ℚ) : ℝ) ≤ Real.log ((464 : ℕ)) / 2 := by
    have h := (log_br_464).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((464 : ℕ)) / 2 ≤ ((30699423/10000000 : ℚ) : ℝ) := by
    have h := (log_br_464).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1040449/10000000) (δ := 3773/500000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t464 : ((21229371621/500000000000 : ℚ) : ℝ) ≤ stT301o2 464 := by
  have hc : ((91459/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((464 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21229371621/500000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((91459/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c465 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((465 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((36917/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30710187/10000000 : ℚ) : ℝ) ≤ Real.log ((465 : ℕ)) / 2 := by
    have h := (log_br_465).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((465 : ℕ)) / 2 ≤ ((491363/160000 : ℚ) : ℝ) := by
    have h := (log_br_465).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 925239/5000000) (δ := 7657/1000000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t465 : ((17118656401/500000000000 : ℚ) : ℝ) ≤ stT301o2 465 := by
  have hc : ((73829/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((465 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17118656401/500000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((73829/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c466 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((466 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((24291/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((960029/312500 : ℚ) : ℝ) ≤ Real.log ((466 : ℕ)) / 2 := by
    have h := (log_br_466).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((466 : ℕ)) / 2 ≤ ((61441857/20000000 : ℚ) : ℝ) := by
    have h := (log_br_466).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1329369/5000000) (δ := 7557/1000000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t466 : ((22502858057/1000000000000 : ℚ) : ℝ) ≤ stT301o2 466 := by
  have hc : ((48577/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((466 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22502858057/1000000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((48577/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c467 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((467 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((183641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15365823/5000000 : ℚ) : ℝ) ≤ Real.log ((467 : ℕ)) / 2 := by
    have h := (log_br_467).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((467 : ℕ)) / 2 ≤ ((61463293/20000000 : ℚ) : ℝ) := by
    have h := (log_br_467).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3465267/10000000) (δ := 481/62500000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t467 : ((10619454213/1250000000000 : ℚ) : ℝ) ≤ stT301o2 467 := by
  have hc : ((183591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((467 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).1
  have hw2 : ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57843/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10619454213/1250000000000 : ℚ) : ℝ)
      = ((57843/1250000 : ℚ) : ℝ) * ((183591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c468 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((468 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-171/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30742341/10000000 : ℚ) : ℝ) ≤ Real.log ((468 : ℕ)) / 2 := by
    have h := (log_br_468).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((468 : ℕ)) / 2 ≤ ((61484683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_468).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2135033/5000000) (δ := 1899/250000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t468 : ((-1265180987/200000000000 : ℚ) : ℝ) ≤ stT301o2 468 := by
  have hc : ((-2737/20000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((468 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1265180987/200000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-2737/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c469 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((469 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-442579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61506027/20000000 : ℚ) : ℝ) ≤ Real.log ((469 : ℕ)) / 2 := by
    have h := (log_br_469).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((469 : ℕ)) / 2 ≤ ((15376507/5000000 : ℚ) : ℝ) := by
    have h := (log_br_469).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1268293/2500000) (δ := 7607/1000000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t469 : ((-102193740891/5000000000000 : ℚ) : ℝ) ≤ stT301o2 469 := by
  have hc : ((-442629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((469 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102193740891/5000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-442629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c470 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((470 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-87823/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30763663/10000000 : ℚ) : ℝ) ≤ Real.log ((470 : ℕ)) / 2 := by
    have h := (log_br_470).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((470 : ℕ)) / 2 ≤ ((61527327/20000000 : ℚ) : ℝ) := by
    have h := (log_br_470).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5874547/10000000) (δ := 7657/1000000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t470 : ((-81025293661/2500000000000 : ℚ) : ℝ) ≤ stT301o2 470 := by
  have hc : ((-351317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((470 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81025293661/2500000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-351317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c471 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((471 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-445353/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3077429/1000000 : ℚ) : ℝ) ≤ Real.log ((471 : ℕ)) / 2 := by
    have h := (log_br_471).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((471 : ℕ)) / 2 ≤ ((61548581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_471).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1668557/2500000) (δ := 481/62500000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t471 : ((-12826218333/312500000000 : ℚ) : ℝ) ≤ stT301o2 471 := by
  have hc : ((-222689/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((471 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12826218333/312500000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-222689/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c472 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((472 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-988363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61569789/20000000 : ℚ) : ℝ) ≤ Real.log ((472 : ℕ)) / 2 := by
    have h := (log_br_472).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((472 : ℕ)) / 2 ≤ ((6156979/2000000 : ℚ) : ℝ) := by
    have h := (log_br_472).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7472217/10000000) (δ := 3773/500000000) (ψ := 1641/200000) 301 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t472 : ((-888583287/19531250000 : ℚ) : ℝ) ≤ stT301o2 472 := by
  have hc : ((-988413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((472 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-888583287/19531250000 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-988413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c473 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((473 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-197257/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61590953/20000000 : ℚ) : ℝ) ≤ Real.log ((473 : ℕ)) / 2 := by
    have h := (log_br_473).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((473 : ℕ)) / 2 ≤ ((30795477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_473).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7439451/10000000) (δ := 7639/1000000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t473 : ((-90703563867/2000000000000 : ℚ) : ℝ) ≤ stT301o2 473 := by
  have hc : ((-197267/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((473 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).2
  have h0 : (0:ℝ) ≤ ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90703563867/2000000000000 : ℚ) : ℝ)
      = ((459801/10000000 : ℚ) : ℝ) * ((-197267/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c474 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((474 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-177059/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61612073/20000000 : ℚ) : ℝ) ≤ Real.log ((474 : ℕ)) / 2 := by
    have h := (log_br_474).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((474 : ℕ)) / 2 ≤ ((30806037/10000000 : ℚ) : ℝ) := by
    have h := (log_br_474).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6644811/10000000) (δ := 7639/1000000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t474 : ((-20332656201/500000000000 : ℚ) : ℝ) ≤ stT301o2 474 := by
  have hc : ((-177069/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((474 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).2
  have h0 : (0:ℝ) ≤ ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20332656201/500000000000 : ℚ) : ℝ)
      = ((114829/2500000 : ℚ) : ℝ) * ((-177069/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c475 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((475 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-696099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15408287/5000000 : ℚ) : ℝ) ≤ Real.log ((475 : ℕ)) / 2 := by
    have h := (log_br_475).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((475 : ℕ)) / 2 ≤ ((61633149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_475).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -731483/1250000) (δ := 7589/1000000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t475 : ((-19963464873/625000000000 : ℚ) : ℝ) ≤ stT301o2 475 := by
  have hc : ((-696149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((475 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).2
  have h0 : (0:ℝ) ≤ ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19963464873/625000000000 : ℚ) : ℝ)
      = ((28677/625000 : ℚ) : ℝ) * ((-696149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c476 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((476 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-438067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30827089/10000000 : ℚ) : ℝ) ≤ Real.log ((476 : ℕ)) / 2 := by
    have h := (log_br_476).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((476 : ℕ)) / 2 ≤ ((61654179/20000000 : ℚ) : ℝ) := by
    have h := (log_br_476).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -506061/1000000) (δ := 1891/250000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t476 : ((-4016218539/200000000000 : ℚ) : ℝ) ≤ stT301o2 476 := by
  have hc : ((-438117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((476 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4016218539/200000000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-438117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c477 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((477 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-5487/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15418791/5000000 : ℚ) : ℝ) ≤ Real.log ((477 : ℕ)) / 2 := by
    have h := (log_br_477).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((477 : ℕ)) / 2 ≤ ((12335033/4000000 : ℚ) : ℝ) := by
    have h := (log_br_477).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1067753/2500000) (δ := 7589/1000000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t477 : ((-2513242941/400000000000 : ℚ) : ℝ) ≤ stT301o2 477 := by
  have hc : ((-5489/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((477 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2513242941/400000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-5489/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c478 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((478 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((44163/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61696107/20000000 : ℚ) : ℝ) ≤ Real.log ((478 : ℕ)) / 2 := by
    have h := (log_br_478).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((478 : ℕ)) / 2 ≤ ((15424027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_478).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3483031/10000000) (δ := 3857/500000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t478 : ((40387906089/5000000000000 : ℚ) : ℝ) ≤ stT301o2 478 := by
  have hc : ((88301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((478 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).1
  have hw2 : ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((457389/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40387906089/5000000000000 : ℚ) : ℝ)
      = ((457389/10000000 : ℚ) : ℝ) * ((88301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c479 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((479 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((472477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12343401/4000000 : ℚ) : ℝ) ≤ Real.log ((479 : ℕ)) / 2 := by
    have h := (log_br_479).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((479 : ℕ)) / 2 ≤ ((30858503/10000000 : ℚ) : ℝ) := by
    have h := (log_br_479).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -337093/1250000) (δ := 3807/500000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t479 : ((215857092997/10000000000000 : ℚ) : ℝ) ≤ stT301o2 479 := by
  have hc : ((472427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((479 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).1
  have hw2 : ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((456911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215857092997/10000000000000 : ℚ) : ℝ)
      = ((456911/10000000 : ℚ) : ℝ) * ((472427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c480 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((480 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((721511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61737861/20000000 : ℚ) : ℝ) ≤ Real.log ((480 : ℕ)) / 2 := by
    have h := (log_br_480).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((480 : ℕ)) / 2 ≤ ((30868931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_480).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1912037/10000000) (δ := 3807/500000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t480 : ((65860010307/2000000000000 : ℚ) : ℝ) ≤ stT301o2 480 := by
  have hc : ((721461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((480 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).1
  have hw2 : ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65860010307/2000000000000 : ℚ) : ℝ)
      = ((91287/2000000 : ℚ) : ℝ) * ((721461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c481 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((481 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((449873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3859917/1250000 : ℚ) : ℝ) ≤ Real.log ((481 : ℕ)) / 2 := by
    have h := (log_br_481).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((481 : ℕ)) / 2 ≤ ((61758673/20000000 : ℚ) : ℝ) := by
    have h := (log_br_481).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1129023/10000000) (δ := 479/62500000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t481 : ((640977169/15625000000 : ℚ) : ℝ) ≤ stT301o2 481 := by
  have hc : ((56231/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((481 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).1
  have hw2 : ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11399/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((640977169/15625000000 : ℚ) : ℝ)
      = ((11399/250000 : ℚ) : ℝ) * ((56231/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c482 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((482 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((19807/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61779441/20000000 : ℚ) : ℝ) ≤ Real.log ((482 : ℕ)) / 2 := by
    have h := (log_br_482).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((482 : ℕ)) / 2 ≤ ((30889721/10000000 : ℚ) : ℝ) := by
    have h := (log_br_482).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -34759/1000000) (δ := 7639/1000000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t482 : ((4510687761/100000000000 : ℚ) : ℝ) ≤ stT301o2 482 := by
  have hc : ((9903/10000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((482 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4510687761/100000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((9903/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c483 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((483 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((492547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30900083/10000000 : ℚ) : ℝ) ≤ Real.log ((483 : ℕ)) / 2 := by
    have h := (log_br_483).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((483 : ℕ)) / 2 ≤ ((61800167/20000000 : ℚ) : ℝ) := by
    have h := (log_br_483).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 108047/2500000) (δ := 7689/1000000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t483 : ((22410489783/500000000000 : ℚ) : ℝ) ≤ stT301o2 483 := by
  have hc : ((246261/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((483 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22410489783/500000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((246261/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c484 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((484 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((885069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61820849/20000000 : ℚ) : ℝ) ≤ Real.log ((484 : ℕ)) / 2 := by
    have h := (log_br_484).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((484 : ℕ)) / 2 ≤ ((1236417/400000 : ℚ) : ℝ) := by
    have h := (log_br_484).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 605193/5000000) (δ := 7639/1000000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t484 : ((80456192271/2000000000000 : ℚ) : ℝ) ≤ stT301o2 484 := by
  have hc : ((885019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((484 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80456192271/2000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((885019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c485 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((485 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((21889/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3865093/1250000 : ℚ) : ℝ) ≤ Real.log ((485 : ℕ)) / 2 := by
    have h := (log_br_485).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((485 : ℕ)) / 2 ≤ ((61841489/20000000 : ℚ) : ℝ) := by
    have h := (log_br_485).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1986929/10000000) (δ := 479/62500000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t485 : ((39754240281/1250000000000 : ℚ) : ℝ) ≤ stT301o2 485 := by
  have hc : ((350199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((485 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39754240281/1250000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((350199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c486 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((486 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((449339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30931043/10000000 : ℚ) : ℝ) ≤ Real.log ((486 : ℕ)) / 2 := by
    have h := (log_br_486).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((486 : ℕ)) / 2 ≤ ((61862087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_486).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 345241/1250000) (δ := 7689/1000000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t486 : ((203801534001/10000000000000 : ℚ) : ℝ) ≤ stT301o2 486 := by
  have hc : ((449289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((486 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203801534001/10000000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((449289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c487 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((487 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((2438/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61882641/20000000 : ℚ) : ℝ) ≤ Real.log ((487 : ℕ)) / 2 := by
    have h := (log_br_487).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((487 : ℕ)) / 2 ≤ ((30941321/10000000 : ℚ) : ℝ) := by
    have h := (log_br_487).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 353531/1000000) (δ := 7639/1000000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t487 : ((35341075713/5000000000000 : ℚ) : ℝ) ≤ stT301o2 487 := by
  have hc : ((77991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((487 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35341075713/5000000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((77991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c488 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((488 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-151463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30951577/10000000 : ℚ) : ℝ) ≤ Real.log ((488 : ℕ)) / 2 := by
    have h := (log_br_488).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((488 : ℕ)) / 2 ≤ ((12380631/4000000 : ℚ) : ℝ) := by
    have h := (log_br_488).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 538389/1250000) (δ := 1891/250000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t488 : ((-68586753327/10000000000000 : ℚ) : ℝ) ≤ stT301o2 488 := by
  have hc : ((-151513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((488 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68586753327/10000000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-151513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c489 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((489 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-444057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7740453/2500000 : ℚ) : ℝ) ≤ Real.log ((489 : ℕ)) / 2 := by
    have h := (log_br_489).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((489 : ℕ)) / 2 ≤ ((495389/160000 : ℚ) : ℝ) := by
    have h := (log_br_489).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 317331/625000) (δ := 479/62500000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t489 : ((-25104036389/1250000000000 : ℚ) : ℝ) ≤ stT301o2 489 := by
  have hc : ((-444107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((489 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25104036389/1250000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-444107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c490 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((490 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-138879/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61944053/20000000 : ℚ) : ℝ) ≤ Real.log ((490 : ℕ)) / 2 := by
    have h := (log_br_490).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((490 : ℕ)) / 2 ≤ ((30972027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_490).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5845937/10000000) (δ := 3807/500000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t490 : ((-31371830653/1000000000000 : ℚ) : ℝ) ≤ stT301o2 490 := by
  have hc : ((-138889/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((490 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31371830653/1000000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-138889/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c491 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((491 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-879313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61964441/20000000 : ℚ) : ℝ) ≤ Real.log ((491 : ℕ)) / 2 := by
    have h := (log_br_491).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((491 : ℕ)) / 2 ≤ ((30982221/10000000 : ℚ) : ℝ) := by
    have h := (log_br_491).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1322607/2000000) (δ := 7639/1000000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t491 : ((-198425622861/5000000000000 : ℚ) : ℝ) ≤ stT301o2 491 := by
  have hc : ((-879363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((491 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198425622861/5000000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-879363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c492 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((492 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-245493/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61984787/20000000 : ℚ) : ℝ) ≤ Real.log ((492 : ℕ)) / 2 := by
    have h := (log_br_492).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((492 : ℕ)) / 2 ≤ ((15496197/5000000 : ℚ) : ℝ) := by
    have h := (log_br_492).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3689277/5000000) (δ := 3857/500000000) (ψ := 1641/200000) 301 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t492 : ((-44272988837/1000000000000 : ℚ) : ℝ) ≤ stT301o2 492 := by
  have hc : ((-491011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((492 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).2
  have h0 : (0:ℝ) ≤ ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44272988837/1000000000000 : ℚ) : ℝ)
      = ((90167/2000000 : ℚ) : ℝ) * ((-491011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c493 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((493 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-248337/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62005091/20000000 : ℚ) : ℝ) ≤ Real.log ((493 : ℕ)) / 2 := by
    have h := (log_br_493).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((493 : ℕ)) / 2 ≤ ((15501273/5000000 : ℚ) : ℝ) := by
    have h := (log_br_493).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -236421/312500) (δ := 477/62500000) (ψ := 1641/200000) 301 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t493 : ((-111851151111/2500000000000 : ℚ) : ℝ) ≤ stT301o2 493 := by
  have hc : ((-496699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((493 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111851151111/2500000000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-496699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c494 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((494 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-182587/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12405071/4000000 : ℚ) : ℝ) ≤ Real.log ((494 : ℕ)) / 2 := by
    have h := (log_br_494).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((494 : ℕ)) / 2 ≤ ((15506339/5000000 : ℚ) : ℝ) := by
    have h := (log_br_494).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6803039/10000000) (δ := 477/62500000) (ψ := 1641/200000) 301 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t494 : ((-41077203717/1000000000000 : ℚ) : ℝ) ≤ stT301o2 494 := by
  have hc : ((-182597/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((494 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41077203717/1000000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-182597/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c495 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((495 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-374343/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62045577/20000000 : ℚ) : ℝ) ≤ Real.log ((495 : ℕ)) / 2 := by
    have h := (log_br_495).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((495 : ℕ)) / 2 ≤ ((31022789/10000000 : ℚ) : ℝ) := by
    have h := (log_br_495).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3021093/5000000) (δ := 1883/250000000) (ψ := 1641/200000) 301 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t495 : ((-5258314433/156250000000 : ℚ) : ℝ) ≤ stT301o2 495 := by
  have hc : ((-11699/15625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((495 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5258314433/156250000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-11699/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c496 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((496 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-516141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62065759/20000000 : ℚ) : ℝ) ≤ Real.log ((496 : ℕ)) / 2 := by
    have h := (log_br_496).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((496 : ℕ)) / 2 ≤ ((387911/125000 : ℚ) : ℝ) := by
    have h := (log_br_496).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2641419/5000000) (δ := 7621/1000000000) (ψ := 1641/200000) 301 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t496 : ((-115888492837/5000000000000 : ℚ) : ℝ) ≤ stT301o2 496 := by
  have hc : ((-516191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((496 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).2
  have h0 : (0:ℝ) ≤ ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115888492837/5000000000000 : ℚ) : ℝ)
      = ((224507/5000000 : ℚ) : ℝ) * ((-516191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c497 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((497 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-118471/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((620859/200000 : ℚ) : ℝ) ≤ Real.log ((497 : ℕ)) / 2 := by
    have h := (log_br_497).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((497 : ℕ)) / 2 ≤ ((62085901/20000000 : ℚ) : ℝ) := by
    have h := (log_br_497).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4525033/10000000) (δ := 7571/1000000000) (ψ := 1641/200000) 301 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t497 : ((-830512543/78125000000 : ℚ) : ℝ) ≤ stT301o2 497 := by
  have hc : ((-3703/15625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((497 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-830512543/78125000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-3703/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c498 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((498 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((31623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((31053/10000 : ℚ) : ℝ) ≤ Real.log ((498 : ℕ)) / 2 := by
    have h := (log_br_498).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((498 : ℕ)) / 2 ≤ ((62106001/20000000 : ℚ) : ℝ) := by
    have h := (log_br_498).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3768771/10000000) (δ := 3841/500000000) (ψ := 1641/200000) 301 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t498 : ((707968989/250000000000 : ℚ) : ℝ) ≤ stT301o2 498 := by
  have hc : ((15799/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((498 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).1
  have hw2 : ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((44811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((707968989/250000000000 : ℚ) : ℝ)
      = ((44811/1000000 : ℚ) : ℝ) * ((15799/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c499 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((499 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((44641/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3106303/1000000 : ℚ) : ℝ) ≤ Real.log ((499 : ℕ)) / 2 := by
    have h := (log_br_499).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((499 : ℕ)) / 2 ≤ ((62126061/20000000 : ℚ) : ℝ) := by
    have h := (log_br_499).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3014013/10000000) (δ := 7571/1000000000) (ψ := 1641/200000) 301 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t499 : ((79924947279/5000000000000 : ℚ) : ℝ) ≤ stT301o2 499 := by
  have hc : ((178539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((499 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).1
  have hw2 : ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79924947279/5000000000000 : ℚ) : ℝ)
      = ((447661/10000000 : ℚ) : ℝ) * ((178539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_c500 :
    |Real.cos (((301 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((77279/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log ((500 : ℕ)) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((500 : ℕ)) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2260761/10000000) (δ := 3841/500000000) (ψ := 1641/200000) 301 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301o2_t500 : ((138229513383/5000000000000 : ℚ) : ℝ) ≤ stT301o2 500 := by
  have hc : ((309091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301o2_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138229513383/5000000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((309091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301o2_p1 : ((249979/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT301o2 (i+1) := by
  rw [Finset.sum_range_one]
  exact st301o2_t1

theorem st301o2_p2 : ((67471990629/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 1, stT301o2 (i+1)) + stT301o2 2 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 1
    simpa using h
  have hprev := st301o2_p1
  have hstep := st301o2_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p3 : ((1036601926359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 2, stT301o2 (i+1)) + stT301o2 3 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 2
    simpa using h
  have hprev := st301o2_p2
  have hstep := st301o2_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p4 : ((1743726926359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 3, stT301o2 (i+1)) + stT301o2 4 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 3
    simpa using h
  have hprev := st301o2_p3
  have hstep := st301o2_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p5 : ((-386159148593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 4, stT301o2 (i+1)) + stT301o2 5 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 4
    simpa using h
  have hprev := st301o2_p4
  have hstep := st301o2_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p6 : ((344921955473/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 5, stT301o2 (i+1)) + stT301o2 6 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 5
    simpa using h
  have hprev := st301o2_p5
  have hstep := st301o2_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p7 : ((-86122763073/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 6, stT301o2 (i+1)) + stT301o2 7 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 6
    simpa using h
  have hprev := st301o2_p6
  have hstep := st301o2_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p8 : ((1070667564471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 7, stT301o2 (i+1)) + stT301o2 8 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 7
    simpa using h
  have hprev := st301o2_p7
  have hstep := st301o2_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p9 : ((-49415849203/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 8, stT301o2 (i+1)) + stT301o2 9 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 8
    simpa using h
  have hprev := st301o2_p8
  have hstep := st301o2_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p10 : ((11786333117/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 9, stT301o2 (i+1)) + stT301o2 10 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 9
    simpa using h
  have hprev := st301o2_p9
  have hstep := st301o2_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p11 : ((-272288467711/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 10, stT301o2 (i+1)) + stT301o2 11 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 10
    simpa using h
  have hprev := st301o2_p10
  have hstep := st301o2_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p12 : ((-630524287279/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 11, stT301o2 (i+1)) + stT301o2 12 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 11
    simpa using h
  have hprev := st301o2_p11
  have hstep := st301o2_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p13 : ((-1519946835029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 12, stT301o2 (i+1)) + stT301o2 13 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 12
    simpa using h
  have hprev := st301o2_p12
  have hstep := st301o2_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p14 : ((-6960573670121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 13, stT301o2 (i+1)) + stT301o2 14 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 13
    simpa using h
  have hprev := st301o2_p13
  have hstep := st301o2_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p15 : ((-5263797018029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 14, stT301o2 (i+1)) + stT301o2 15 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 14
    simpa using h
  have hprev := st301o2_p14
  have hstep := st301o2_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p16 : ((-3687415181221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 15, stT301o2 (i+1)) + stT301o2 16 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 15
    simpa using h
  have hprev := st301o2_p15
  have hstep := st301o2_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p17 : ((-2901989106859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 16, stT301o2 (i+1)) + stT301o2 17 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 16
    simpa using h
  have hprev := st301o2_p16
  have hstep := st301o2_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p18 : ((-345436753709/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 17, stT301o2 (i+1)) + stT301o2 18 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 17
    simpa using h
  have hprev := st301o2_p17
  have hstep := st301o2_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p19 : ((-973748924213/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 18, stT301o2 (i+1)) + stT301o2 19 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 18
    simpa using h
  have hprev := st301o2_p18
  have hstep := st301o2_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p20 : ((-3860450697769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 19, stT301o2 (i+1)) + stT301o2 20 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 19
    simpa using h
  have hprev := st301o2_p19
  have hstep := st301o2_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p21 : ((-361595892117/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 20, stT301o2 (i+1)) + stT301o2 21 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 20
    simpa using h
  have hprev := st301o2_p20
  have hstep := st301o2_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p22 : ((-464214761937/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 21, stT301o2 (i+1)) + stT301o2 22 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 21
    simpa using h
  have hprev := st301o2_p21
  have hstep := st301o2_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p23 : ((-127956914277/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 22, stT301o2 (i+1)) + stT301o2 23 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 22
    simpa using h
  have hprev := st301o2_p22
  have hstep := st301o2_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p24 : ((-288733028299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 23, stT301o2 (i+1)) + stT301o2 24 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 23
    simpa using h
  have hprev := st301o2_p23
  have hstep := st301o2_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p25 : ((520807971701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 24, stT301o2 (i+1)) + stT301o2 25 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 24
    simpa using h
  have hprev := st301o2_p24
  have hstep := st301o2_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p26 : ((1471610203077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 25, stT301o2 (i+1)) + stT301o2 26 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 25
    simpa using h
  have hprev := st301o2_p25
  have hstep := st301o2_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p27 : ((2373344300577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 26, stT301o2 (i+1)) + stT301o2 27 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 26
    simpa using h
  have hprev := st301o2_p26
  have hstep := st301o2_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p28 : ((686305159751/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 27, stT301o2 (i+1)) + stT301o2 28 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 27
    simpa using h
  have hprev := st301o2_p27
  have hstep := st301o2_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p29 : ((2222916115901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 28, stT301o2 (i+1)) + stT301o2 29 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 28
    simpa using h
  have hprev := st301o2_p28
  have hstep := st301o2_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p30 : ((664800775667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 29, stT301o2 (i+1)) + stT301o2 30 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 29
    simpa using h
  have hprev := st301o2_p29
  have hstep := st301o2_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p31 : ((329047604029/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 30, stT301o2 (i+1)) + stT301o2 31 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 30
    simpa using h
  have hprev := st301o2_p30
  have hstep := st301o2_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p32 : ((43943096689/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 31, stT301o2 (i+1)) + stT301o2 32 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 31
    simpa using h
  have hprev := st301o2_p31
  have hstep := st301o2_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p33 : ((2196599526587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 32, stT301o2 (i+1)) + stT301o2 33 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 32
    simpa using h
  have hprev := st301o2_p32
  have hstep := st301o2_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p34 : ((679875335281/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 33, stT301o2 (i+1)) + stT301o2 34 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 33
    simpa using h
  have hprev := st301o2_p33
  have hstep := st301o2_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p35 : ((453922108601/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 34, stT301o2 (i+1)) + stT301o2 35 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 34
    simpa using h
  have hprev := st301o2_p34
  have hstep := st301o2_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p36 : ((1117834966539/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 35, stT301o2 (i+1)) + stT301o2 36 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 35
    simpa using h
  have hprev := st301o2_p35
  have hstep := st301o2_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p37 : ((1415142194153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 36, stT301o2 (i+1)) + stT301o2 37 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 36
    simpa using h
  have hprev := st301o2_p36
  have hstep := st301o2_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p38 : ((1973542319447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 37, stT301o2 (i+1)) + stT301o2 38 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 37
    simpa using h
  have hprev := st301o2_p37
  have hstep := st301o2_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p39 : ((3960316023797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 38, stT301o2 (i+1)) + stT301o2 39 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 38
    simpa using h
  have hprev := st301o2_p38
  have hstep := st301o2_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p40 : ((2969659707903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 39, stT301o2 (i+1)) + stT301o2 40 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 39
    simpa using h
  have hprev := st301o2_p39
  have hstep := st301o2_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p41 : ((2226238726041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 40, stT301o2 (i+1)) + stT301o2 41 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 40
    simpa using h
  have hprev := st301o2_p40
  have hstep := st301o2_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p42 : ((366321912839/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 41, stT301o2 (i+1)) + stT301o2 42 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 41
    simpa using h
  have hprev := st301o2_p41
  have hstep := st301o2_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p43 : ((2108939595291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 42, stT301o2 (i+1)) + stT301o2 43 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 42
    simpa using h
  have hprev := st301o2_p42
  have hstep := st301o2_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p44 : ((652399218321/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 43, stT301o2 (i+1)) + stT301o2 44 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 43
    simpa using h
  have hprev := st301o2_p43
  have hstep := st301o2_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p45 : ((781035651933/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 44, stT301o2 (i+1)) + stT301o2 45 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 44
    simpa using h
  have hprev := st301o2_p44
  have hstep := st301o2_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p46 : ((139909363521/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 45, stT301o2 (i+1)) + stT301o2 46 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 45
    simpa using h
  have hprev := st301o2_p45
  have hstep := st301o2_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p47 : ((3765728751497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 46, stT301o2 (i+1)) + stT301o2 47 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 46
    simpa using h
  have hprev := st301o2_p46
  have hstep := st301o2_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p48 : ((3538716017593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 47, stT301o2 (i+1)) + stT301o2 48 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 47
    simpa using h
  have hprev := st301o2_p47
  have hstep := st301o2_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p49 : ((1908628681301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 48, stT301o2 (i+1)) + stT301o2 49 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 48
    simpa using h
  have hprev := st301o2_p48
  have hstep := st301o2_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p50 : ((1701413803379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 49, stT301o2 (i+1)) + stT301o2 50 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 49
    simpa using h
  have hprev := st301o2_p49
  have hstep := st301o2_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p51 : ((2011363680959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 50, stT301o2 (i+1)) + stT301o2 51 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 50
    simpa using h
  have hprev := st301o2_p50
  have hstep := st301o2_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p52 : ((630604462403/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 51, stT301o2 (i+1)) + stT301o2 52 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 51
    simpa using h
  have hprev := st301o2_p51
  have hstep := st301o2_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p53 : ((854478451397/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 52, stT301o2 (i+1)) + stT301o2 53 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 52
    simpa using h
  have hprev := st301o2_p52
  have hstep := st301o2_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p54 : ((593640383669/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 53, stT301o2 (i+1)) + stT301o2 54 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 53
    simpa using h
  have hprev := st301o2_p53
  have hstep := st301o2_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p55 : ((2155516689437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 54, stT301o2 (i+1)) + stT301o2 55 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 54
    simpa using h
  have hprev := st301o2_p54
  have hstep := st301o2_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p56 : ((1575701099979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 55, stT301o2 (i+1)) + stT301o2 56 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 55
    simpa using h
  have hprev := st301o2_p55
  have hstep := st301o2_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p57 : ((1934624105871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 56, stT301o2 (i+1)) + stT301o2 57 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 56
    simpa using h
  have hprev := st301o2_p56
  have hstep := st301o2_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p58 : ((237828581377/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 57, stT301o2 (i+1)) + stT301o2 58 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 57
    simpa using h
  have hprev := st301o2_p57
  have hstep := st301o2_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p59 : ((197381462857/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 58, stT301o2 (i+1)) + stT301o2 59 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 58
    simpa using h
  have hprev := st301o2_p58
  have hstep := st301o2_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p60 : ((270431067353/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 59, stT301o2 (i+1)) + stT301o2 60 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 59
    simpa using h
  have hprev := st301o2_p59
  have hstep := st301o2_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p61 : ((153803181487/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 60, stT301o2 (i+1)) + stT301o2 61 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 60
    simpa using h
  have hprev := st301o2_p60
  have hstep := st301o2_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p62 : ((3855627073569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 61, stT301o2 (i+1)) + stT301o2 62 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 61
    simpa using h
  have hprev := st301o2_p61
  have hstep := st301o2_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p63 : ((1973454615831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 62, stT301o2 (i+1)) + stT301o2 63 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 62
    simpa using h
  have hprev := st301o2_p62
  have hstep := st301o2_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p64 : ((1506339242139/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 63, stT301o2 (i+1)) + stT301o2 64 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 63
    simpa using h
  have hprev := st301o2_p63
  have hstep := st301o2_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p65 : ((1062212619069/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 64, stT301o2 (i+1)) + stT301o2 65 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 64
    simpa using h
  have hprev := st301o2_p64
  have hstep := st301o2_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p66 : ((1754132771433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 65, stT301o2 (i+1)) + stT301o2 66 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 65
    simpa using h
  have hprev := st301o2_p65
  have hstep := st301o2_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p67 : ((1613129621313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 66, stT301o2 (i+1)) + stT301o2 67 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 66
    simpa using h
  have hprev := st301o2_p66
  have hstep := st301o2_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p68 : ((433049715051/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 67, stT301o2 (i+1)) + stT301o2 68 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 67
    simpa using h
  have hprev := st301o2_p67
  have hstep := st301o2_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p69 : ((1642398165247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 68, stT301o2 (i+1)) + stT301o2 69 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 68
    simpa using h
  have hprev := st301o2_p68
  have hstep := st301o2_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p70 : ((1687877188261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 69, stT301o2 (i+1)) + stT301o2 70 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 69
    simpa using h
  have hprev := st301o2_p69
  have hstep := st301o2_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p71 : ((2163728898021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 70, stT301o2 (i+1)) + stT301o2 71 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 70
    simpa using h
  have hprev := st301o2_p70
  have hstep := st301o2_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p72 : ((1620146130581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 71, stT301o2 (i+1)) + stT301o2 72 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 71
    simpa using h
  have hprev := st301o2_p71
  have hstep := st301o2_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p73 : ((336715076863/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 72, stT301o2 (i+1)) + stT301o2 73 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 72
    simpa using h
  have hprev := st301o2_p72
  have hstep := st301o2_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p74 : ((2167971577421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 73, stT301o2 (i+1)) + stT301o2 74 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 73
    simpa using h
  have hprev := st301o2_p73
  have hstep := st301o2_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p75 : ((417884187499/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 74, stT301o2 (i+1)) + stT301o2 75 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 74
    simpa using h
  have hprev := st301o2_p74
  have hstep := st301o2_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p76 : ((3213317070591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 75, stT301o2 (i+1)) + stT301o2 76 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 75
    simpa using h
  have hprev := st301o2_p75
  have hstep := st301o2_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p77 : ((4307456389511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 76, stT301o2 (i+1)) + stT301o2 77 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 76
    simpa using h
  have hprev := st301o2_p76
  have hstep := st301o2_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p78 : ((3618193479791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 77, stT301o2 (i+1)) + stT301o2 78 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 77
    simpa using h
  have hprev := st301o2_p77
  have hstep := st301o2_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p79 : ((602207498083/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 78, stT301o2 (i+1)) + stT301o2 79 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 78
    simpa using h
  have hprev := st301o2_p78
  have hstep := st301o2_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p80 : ((127965766249/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 79, stT301o2 (i+1)) + stT301o2 80 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 79
    simpa using h
  have hprev := st301o2_p79
  have hstep := st301o2_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p81 : ((252378335211/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 80, stT301o2 (i+1)) + stT301o2 81 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 80
    simpa using h
  have hprev := st301o2_p80
  have hstep := st301o2_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p82 : ((748049134867/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 81, stT301o2 (i+1)) + stT301o2 82 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 81
    simpa using h
  have hprev := st301o2_p81
  have hstep := st301o2_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p83 : ((898525974289/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 82, stT301o2 (i+1)) + stT301o2 83 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 82
    simpa using h
  have hprev := st301o2_p82
  have hstep := st301o2_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p84 : ((543088457977/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 83, stT301o2 (i+1)) + stT301o2 84 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 83
    simpa using h
  have hprev := st301o2_p83
  have hstep := st301o2_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p85 : ((854767283057/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 84, stT301o2 (i+1)) + stT301o2 85 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 84
    simpa using h
  have hprev := st301o2_p84
  have hstep := st301o2_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p86 : ((760045603627/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 85, stT301o2 (i+1)) + stT301o2 86 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 85
    simpa using h
  have hprev := st301o2_p85
  have hstep := st301o2_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p87 : ((204648801419/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 86, stT301o2 (i+1)) + stT301o2 87 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 86
    simpa using h
  have hprev := st301o2_p86
  have hstep := st301o2_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p88 : ((258514118881/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 87, stT301o2 (i+1)) + stT301o2 88 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 87
    simpa using h
  have hprev := st301o2_p87
  have hstep := st301o2_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p89 : ((1540192077127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 88, stT301o2 (i+1)) + stT301o2 89 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 88
    simpa using h
  have hprev := st301o2_p88
  have hstep := st301o2_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p90 : ((1644837587473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 89, stT301o2 (i+1)) + stT301o2 90 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 89
    simpa using h
  have hprev := st301o2_p89
  have hstep := st301o2_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p91 : ((85869840319/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 90, stT301o2 (i+1)) + stT301o2 91 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 90
    simpa using h
  have hprev := st301o2_p90
  have hstep := st301o2_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p92 : ((784032452649/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 91, stT301o2 (i+1)) + stT301o2 92 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 91
    simpa using h
  have hprev := st301o2_p91
  have hstep := st301o2_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p93 : ((594860262337/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 92, stT301o2 (i+1)) + stT301o2 93 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 92
    simpa using h
  have hprev := st301o2_p92
  have hstep := st301o2_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p94 : ((686660857021/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 93, stT301o2 (i+1)) + stT301o2 94 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 93
    simpa using h
  have hprev := st301o2_p93
  have hstep := st301o2_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p95 : ((4341835505511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 94, stT301o2 (i+1)) + stT301o2 95 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 94
    simpa using h
  have hprev := st301o2_p94
  have hstep := st301o2_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p96 : ((3863078524347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 95, stT301o2 (i+1)) + stT301o2 96 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 95
    simpa using h
  have hprev := st301o2_p95
  have hstep := st301o2_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p97 : ((185063679117/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 96, stT301o2 (i+1)) + stT301o2 97 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 96
    simpa using h
  have hprev := st301o2_p96
  have hstep := st301o2_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p98 : ((425021922101/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 97, stT301o2 (i+1)) + stT301o2 98 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 97
    simpa using h
  have hprev := st301o2_p97
  have hstep := st301o2_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p99 : ((4323083768279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 98, stT301o2 (i+1)) + stT301o2 99 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 98
    simpa using h
  have hprev := st301o2_p98
  have hstep := st301o2_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p100 : ((3981336768279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 99, stT301o2 (i+1)) + stT301o2 100 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 99
    simpa using h
  have hprev := st301o2_p99
  have hstep := st301o2_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p101 : ((3023761948979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 100, stT301o2 (i+1)) + stT301o2 101 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 100
    simpa using h
  have hprev := st301o2_p100
  have hstep := st301o2_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p102 : ((802054355939/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 101, stT301o2 (i+1)) + stT301o2 102 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 101
    simpa using h
  have hprev := st301o2_p101
  have hstep := st301o2_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p103 : ((4189945046261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 102, stT301o2 (i+1)) + stT301o2 103 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 102
    simpa using h
  have hprev := st301o2_p102
  have hstep := st301o2_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p104 : ((4221021587621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 103, stT301o2 (i+1)) + stT301o2 104 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 103
    simpa using h
  have hprev := st301o2_p103
  have hstep := st301o2_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p105 : ((1628950981509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 104, stT301o2 (i+1)) + stT301o2 105 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 104
    simpa using h
  have hprev := st301o2_p104
  have hstep := st301o2_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p106 : ((1482356728101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 105, stT301o2 (i+1)) + stT301o2 106 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 105
    simpa using h
  have hprev := st301o2_p105
  have hstep := st301o2_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p107 : ((1914546690997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 106, stT301o2 (i+1)) + stT301o2 107 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 106
    simpa using h
  have hprev := st301o2_p106
  have hstep := st301o2_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p108 : ((2199916362247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 107, stT301o2 (i+1)) + stT301o2 108 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 107
    simpa using h
  have hprev := st301o2_p107
  have hstep := st301o2_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p109 : ((3745425203727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 108, stT301o2 (i+1)) + stT301o2 109 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 108
    simpa using h
  have hprev := st301o2_p108
  have hstep := st301o2_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p110 : ((2935401177447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 109, stT301o2 (i+1)) + stT301o2 110 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 109
    simpa using h
  have hprev := st301o2_p109
  have hstep := st301o2_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p111 : ((814525080023/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 110, stT301o2 (i+1)) + stT301o2 111 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 110
    simpa using h
  have hprev := st301o2_p110
  have hstep := st301o2_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p112 : ((4195481324333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 111, stT301o2 (i+1)) + stT301o2 112 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 111
    simpa using h
  have hprev := st301o2_p111
  have hstep := st301o2_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p113 : ((4295964331133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 112, stT301o2 (i+1)) + stT301o2 113 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 112
    simpa using h
  have hprev := st301o2_p112
  have hstep := st301o2_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p114 : ((3416716126053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 113, stT301o2 (i+1)) + stT301o2 114 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 113
    simpa using h
  have hprev := st301o2_p113
  have hstep := st301o2_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p115 : ((2883810033663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 114, stT301o2 (i+1)) + stT301o2 115 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 114
    simpa using h
  have hprev := st301o2_p114
  have hstep := st301o2_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p116 : ((3478191586107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 115, stT301o2 (i+1)) + stT301o2 116 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 115
    simpa using h
  have hprev := st301o2_p115
  have hstep := st301o2_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p117 : ((4323852999607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 116, stT301o2 (i+1)) + stT301o2 117 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 116
    simpa using h
  have hprev := st301o2_p116
  have hstep := st301o2_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p118 : ((2104100120891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 117, stT301o2 (i+1)) + stT301o2 118 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 117
    simpa using h
  have hprev := st301o2_p117
  have hstep := st301o2_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p119 : ((1652715699893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 118, stT301o2 (i+1)) + stT301o2 119 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 118
    simpa using h
  have hprev := st301o2_p118
  have hstep := st301o2_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p120 : ((2878820308227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 119, stT301o2 (i+1)) + stT301o2 120 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 119
    simpa using h
  have hprev := st301o2_p119
  have hstep := st301o2_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p121 : ((3506881498347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 120, stT301o2 (i+1)) + stT301o2 121 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 120
    simpa using h
  have hprev := st301o2_p120
  have hstep := st301o2_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p122 : ((2164763899449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 121, stT301o2 (i+1)) + stT301o2 122 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 121
    simpa using h
  have hprev := st301o2_p121
  have hstep := st301o2_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p123 : ((2124924512169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 122, stT301o2 (i+1)) + stT301o2 123 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 122
    simpa using h
  have hprev := st301o2_p122
  have hstep := st301o2_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p124 : ((3382828202567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 123, stT301o2 (i+1)) + stT301o2 124 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 123
    simpa using h
  have hprev := st301o2_p123
  have hstep := st301o2_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p125 : ((2858959039683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 124, stT301o2 (i+1)) + stT301o2 125 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 124
    simpa using h
  have hprev := st301o2_p124
  have hstep := st301o2_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p126 : ((3342300558183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 125, stT301o2 (i+1)) + stT301o2 126 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 125
    simpa using h
  have hprev := st301o2_p125
  have hstep := st301o2_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p127 : ((4213230711267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 126, stT301o2 (i+1)) + stT301o2 127 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 126
    simpa using h
  have hprev := st301o2_p126
  have hstep := st301o2_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p128 : ((4387005644599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 127, stT301o2 (i+1)) + stT301o2 128 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 127
    simpa using h
  have hprev := st301o2_p127
  have hstep := st301o2_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p129 : ((731812569003/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 128, stT301o2 (i+1)) + stT301o2 129 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 128
    simpa using h
  have hprev := st301o2_p128
  have hstep := st301o2_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p130 : ((1459048106493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 129, stT301o2 (i+1)) + stT301o2 130 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 129
    simpa using h
  have hprev := st301o2_p129
  have hstep := st301o2_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p131 : ((304612093381/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 130, stT301o2 (i+1)) + stT301o2 131 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 130
    simpa using h
  have hprev := st301o2_p130
  have hstep := st301o2_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p132 : ((1941381125137/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 131, stT301o2 (i+1)) + stT301o2 132 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 131
    simpa using h
  have hprev := st301o2_p131
  have hstep := st301o2_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p133 : ((44506440739/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 132, stT301o2 (i+1)) + stT301o2 133 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 132
    simpa using h
  have hprev := st301o2_p132
  have hstep := st301o2_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p134 : ((4103715147369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 133, stT301o2 (i+1)) + stT301o2 134 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 133
    simpa using h
  have hprev := st301o2_p133
  have hstep := st301o2_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p135 : ((3243651168817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 134, stT301o2 (i+1)) + stT301o2 135 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 134
    simpa using h
  have hprev := st301o2_p134
  have hstep := st301o2_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p136 : ((2833467677281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 135, stT301o2 (i+1)) + stT301o2 136 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 135
    simpa using h
  have hprev := st301o2_p135
  have hstep := st301o2_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p137 : ((663709531977/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 136, stT301o2 (i+1)) + stT301o2 137 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 136
    simpa using h
  have hprev := st301o2_p136
  have hstep := st301o2_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p138 : ((832568077161/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 137, stT301o2 (i+1)) + stT301o2 138 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 137
    simpa using h
  have hprev := st301o2_p137
  have hstep := st301o2_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p139 : ((4458842730421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 138, stT301o2 (i+1)) + stT301o2 139 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 138
    simpa using h
  have hprev := st301o2_p138
  have hstep := st301o2_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p140 : ((3900044837831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 139, stT301o2 (i+1)) + stT301o2 140 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 139
    simpa using h
  have hprev := st301o2_p139
  have hstep := st301o2_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p141 : ((3078646831719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 140, stT301o2 (i+1)) + stT301o2 141 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 140
    simpa using h
  have hprev := st301o2_p140
  have hstep := st301o2_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p142 : ((113722967129/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 141, stT301o2 (i+1)) + stT301o2 142 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 141
    simpa using h
  have hprev := st301o2_p141
  have hstep := st301o2_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p143 : ((3426165655017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 142, stT301o2 (i+1)) + stT301o2 143 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 142
    simpa using h
  have hprev := st301o2_p142
  have hstep := st301o2_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p144 : ((4233625332033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 143, stT301o2 (i+1)) + stT301o2 144 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 143
    simpa using h
  have hprev := st301o2_p143
  have hstep := st301o2_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p145 : ((4462784130609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 144, stT301o2 (i+1)) + stT301o2 145 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 144
    simpa using h
  have hprev := st301o2_p144
  have hstep := st301o2_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p146 : ((3895745741679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 145, stT301o2 (i+1)) + stT301o2 146 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 145
    simpa using h
  have hprev := st301o2_p145
  have hstep := st301o2_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p147 : ((3089252517339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 146, stT301o2 (i+1)) + stT301o2 147 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 146
    simpa using h
  have hprev := st301o2_p146
  have hstep := st301o2_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p148 : ((87990778477/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 147, stT301o2 (i+1)) + stT301o2 148 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 147
    simpa using h
  have hprev := st301o2_p147
  have hstep := st301o2_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p149 : ((3327138536099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 148, stT301o2 (i+1)) + stT301o2 149 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 148
    simpa using h
  have hprev := st301o2_p148
  have hstep := st301o2_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p150 : ((4138644112547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 149, stT301o2 (i+1)) + stT301o2 150 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 149
    simpa using h
  have hprev := st301o2_p149
  have hstep := st301o2_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p151 : ((4500335444299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 150, stT301o2 (i+1)) + stT301o2 151 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 150
    simpa using h
  have hprev := st301o2_p150
  have hstep := st301o2_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p152 : ((4088305558027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 151, stT301o2 (i+1)) + stT301o2 152 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 151
    simpa using h
  have hprev := st301o2_p151
  have hstep := st301o2_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p153 : ((656173594999/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 152, stT301o2 (i+1)) + stT301o2 153 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 152
    simpa using h
  have hprev := st301o2_p152
  have hstep := st301o2_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p154 : ((87457906753/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 153, stT301o2 (i+1)) + stT301o2 154 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 153
    simpa using h
  have hprev := st301o2_p153
  have hstep := st301o2_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p155 : ((3060906429253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 154, stT301o2 (i+1)) + stT301o2 155 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 154
    simpa using h
  have hprev := st301o2_p154
  have hstep := st301o2_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p156 : ((3832437560773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 155, stT301o2 (i+1)) + stT301o2 156 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 155
    simpa using h
  have hprev := st301o2_p155
  have hstep := st301o2_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p157 : ((4447219966379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 156, stT301o2 (i+1)) + stT301o2 157 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 156
    simpa using h
  have hprev := st301o2_p156
  have hstep := st301o2_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p158 : ((877334327623/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 157, stT301o2 (i+1)) + stT301o2 158 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 157
    simpa using h
  have hprev := st301o2_p157
  have hstep := st301o2_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p159 : ((741704988479/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 158, stT301o2 (i+1)) + stT301o2 159 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 158
    simpa using h
  have hprev := st301o2_p158
  have hstep := st301o2_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p160 : ((119193756971/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 159, stT301o2 (i+1)) + stT301o2 160 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 159
    simpa using h
  have hprev := st301o2_p159
  have hstep := st301o2_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p161 : ((2796557677671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 160, stT301o2 (i+1)) + stT301o2 161 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 160
    simpa using h
  have hprev := st301o2_p160
  have hstep := st301o2_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p162 : ((3300999669371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 161, stT301o2 (i+1)) + stT301o2 162 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 161
    simpa using h
  have hprev := st301o2_p161
  have hstep := st301o2_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p163 : ((4083137257791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 162, stT301o2 (i+1)) + stT301o2 163 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 162
    simpa using h
  have hprev := st301o2_p162
  have hstep := st301o2_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p164 : ((4522530900523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 163, stT301o2 (i+1)) + stT301o2 164 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 163
    simpa using h
  have hprev := st301o2_p163
  have hstep := st301o2_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p165 : ((4279685922463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 164, stT301o2 (i+1)) + stT301o2 165 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 164
    simpa using h
  have hprev := st301o2_p164
  have hstep := st301o2_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p166 : ((1774516835117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 165, stT301o2 (i+1)) + stT301o2 166 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 165
    simpa using h
  have hprev := st301o2_p165
  have hstep := st301o2_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p167 : ((289323253289/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 166, stT301o2 (i+1)) + stT301o2 167 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 166
    simpa using h
  have hprev := st301o2_p166
  have hstep := st301o2_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p168 : ((2806483932927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 167, stT301o2 (i+1)) + stT301o2 168 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 167
    simpa using h
  have hprev := st301o2_p167
  have hstep := st301o2_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p169 : ((3347735699367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 168, stT301o2 (i+1)) + stT301o2 169 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 168
    simpa using h
  have hprev := st301o2_p168
  have hstep := st301o2_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p170 : ((4111006000743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 169, stT301o2 (i+1)) + stT301o2 170 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 169
    simpa using h
  have hprev := st301o2_p169
  have hstep := st301o2_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p171 : ((907340119407/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 170, stT301o2 (i+1)) + stT301o2 171 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 170
    simpa using h
  have hprev := st301o2_p170
  have hstep := st301o2_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p172 : ((4320730554729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 171, stT301o2 (i+1)) + stT301o2 172 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 171
    simpa using h
  have hprev := st301o2_p171
  have hstep := st301o2_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p173 : ((3623786262247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 172, stT301o2 (i+1)) + stT301o2 173 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 172
    simpa using h
  have hprev := st301o2_p172
  have hstep := st301o2_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p174 : ((2943186206819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 173, stT301o2 (i+1)) + stT301o2 174 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 173
    simpa using h
  have hprev := st301o2_p173
  have hstep := st301o2_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p175 : ((1377295118269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 174, stT301o2 (i+1)) + stT301o2 175 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 174
    simpa using h
  have hprev := st301o2_p174
  have hstep := st301o2_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p176 : ((1591775110389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 175, stT301o2 (i+1)) + stT301o2 176 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 175
    simpa using h
  have hprev := st301o2_p175
  have hstep := st301o2_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p177 : ((393039470613/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 176, stT301o2 (i+1)) + stT301o2 177 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 176
    simpa using h
  have hprev := st301o2_p176
  have hstep := st301o2_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p178 : ((4486261136819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 177, stT301o2 (i+1)) + stT301o2 178 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 177
    simpa using h
  have hprev := st301o2_p177
  have hstep := st301o2_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p179 : ((4480549978343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 178, stT301o2 (i+1)) + stT301o2 179 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 178
    simpa using h
  have hprev := st301o2_p178
  have hstep := st301o2_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p180 : ((3922500450431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 179, stT301o2 (i+1)) + stT301o2 180 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 179
    simpa using h
  have hprev := st301o2_p179
  have hstep := st301o2_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p181 : ((3183581971391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 180, stT301o2 (i+1)) + stT301o2 181 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 180
    simpa using h
  have hprev := st301o2_p180
  have hstep := st301o2_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p182 : ((2745303083891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 181, stT301o2 (i+1)) + stT301o2 182 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 181
    simpa using h
  have hprev := st301o2_p181
  have hstep := st301o2_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p183 : ((577278752167/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 182, stT301o2 (i+1)) + stT301o2 183 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 182
    simpa using h
  have hprev := st301o2_p182
  have hstep := st301o2_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p184 : ((438941623233/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 183, stT301o2 (i+1)) + stT301o2 184 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 183
    simpa using h
  have hprev := st301o2_p183
  have hstep := st301o2_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p185 : ((422252830149/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 184, stT301o2 (i+1)) + stT301o2 185 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 184
    simpa using h
  have hprev := st301o2_p184
  have hstep := st301o2_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p186 : ((915099619687/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 185, stT301o2 (i+1)) + stT301o2 186 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 185
    simpa using h
  have hprev := st301o2_p185
  have hstep := st301o2_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p187 : ((87121665823/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 186, stT301o2 (i+1)) + stT301o2 187 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 186
    simpa using h
  have hprev := st301o2_p186
  have hstep := st301o2_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p188 : ((29629225711/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 187, stT301o2 (i+1)) + stT301o2 188 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 187
    simpa using h
  have hprev := st301o2_p187
  have hstep := st301o2_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p189 : ((603330469433/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 188, stT301o2 (i+1)) + stT301o2 189 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 188
    simpa using h
  have hprev := st301o2_p188
  have hstep := st301o2_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p190 : ((1353265984249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 189, stT301o2 (i+1)) + stT301o2 190 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 189
    simpa using h
  have hprev := st301o2_p189
  have hstep := st301o2_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p191 : ((184594840077/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 190, stT301o2 (i+1)) + stT301o2 191 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 190
    simpa using h
  have hprev := st301o2_p190
  have hstep := st301o2_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p192 : ((3607499375327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 191, stT301o2 (i+1)) + stT301o2 192 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 191
    simpa using h
  have hprev := st301o2_p191
  have hstep := st301o2_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p193 : ((133899593291/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 192, stT301o2 (i+1)) + stT301o2 193 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 192
    simpa using h
  have hprev := st301o2_p192
  have hstep := st301o2_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p194 : ((1148887340487/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 193, stT301o2 (i+1)) + stT301o2 194 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 193
    simpa using h
  have hprev := st301o2_p193
  have hstep := st301o2_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p195 : ((1091529393447/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 194, stT301o2 (i+1)) + stT301o2 195 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 194
    simpa using h
  have hprev := st301o2_p194
  have hstep := st301o2_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p196 : ((932709329919/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 195, stT301o2 (i+1)) + stT301o2 196 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 195
    simpa using h
  have hprev := st301o2_p195
  have hstep := st301o2_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p197 : ((1524144338367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 196, stT301o2 (i+1)) + stT301o2 197 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 196
    simpa using h
  have hprev := st301o2_p196
  have hstep := st301o2_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p198 : ((1348261330737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 197, stT301o2 (i+1)) + stT301o2 198 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 197
    simpa using h
  have hprev := st301o2_p197
  have hstep := st301o2_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p199 : ((2865290923311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 198, stT301o2 (i+1)) + stT301o2 199 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 198
    simpa using h
  have hprev := st301o2_p198
  have hstep := st301o2_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p200 : ((3458277085971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 199, stT301o2 (i+1)) + stT301o2 200 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 199
    simpa using h
  have hprev := st301o2_p199
  have hstep := st301o2_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p201 : ((4152855699891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 200, stT301o2 (i+1)) + stT301o2 201 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 200
    simpa using h
  have hprev := st301o2_p200
  have hstep := st301o2_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p202 : ((915641927493/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 201, stT301o2 (i+1)) + stT301o2 202 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 201
    simpa using h
  have hprev := st301o2_p201
  have hstep := st301o2_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p203 : ((4512324353929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 202, stT301o2 (i+1)) + stT301o2 203 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 202
    simpa using h
  have hprev := st301o2_p202
  have hstep := st301o2_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p204 : ((1996987132219/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 203, stT301o2 (i+1)) + stT301o2 204 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 203
    simpa using h
  have hprev := st301o2_p203
  have hstep := st301o2_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p205 : ((3295509041319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 204, stT301o2 (i+1)) + stT301o2 205 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 204
    simpa using h
  have hprev := st301o2_p204
  have hstep := st301o2_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p206 : ((2776764102427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 205, stT301o2 (i+1)) + stT301o2 206 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 205
    simpa using h
  have hprev := st301o2_p205
  have hstep := st301o2_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p207 : ((337470908657/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 206, stT301o2 (i+1)) + stT301o2 207 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 206
    simpa using h
  have hprev := st301o2_p206
  have hstep := st301o2_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p208 : ((193713248641/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 207, stT301o2 (i+1)) + stT301o2 208 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 207
    simpa using h
  have hprev := st301o2_p207
  have hstep := st301o2_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p209 : ((1886070252049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 208, stT301o2 (i+1)) + stT301o2 209 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 208
    simpa using h
  have hprev := st301o2_p208
  have hstep := st301o2_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p210 : ((4382986732163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 209, stT301o2 (i+1)) + stT301o2 210 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 209
    simpa using h
  have hprev := st301o2_p209
  have hstep := st301o2_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p211 : ((926645235919/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 210, stT301o2 (i+1)) + stT301o2 211 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 210
    simpa using h
  have hprev := st301o2_p210
  have hstep := st301o2_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p212 : ((440446927037/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 211, stT301o2 (i+1)) + stT301o2 212 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 211
    simpa using h
  have hprev := st301o2_p211
  have hstep := st301o2_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p213 : ((3810855095031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 212, stT301o2 (i+1)) + stT301o2 213 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 212
    simpa using h
  have hprev := st301o2_p212
  have hstep := st301o2_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p214 : ((627701996643/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 213, stT301o2 (i+1)) + stT301o2 214 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 213
    simpa using h
  have hprev := st301o2_p213
  have hstep := st301o2_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p215 : ((108231584467/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 214, stT301o2 (i+1)) + stT301o2 215 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 214
    simpa using h
  have hprev := st301o2_p214
  have hstep := st301o2_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p216 : ((1356651706217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 215, stT301o2 (i+1)) + stT301o2 216 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 215
    simpa using h
  have hprev := st301o2_p215
  have hstep := st301o2_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p217 : ((1576911466989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 216, stT301o2 (i+1)) + stT301o2 217 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 216
    simpa using h
  have hprev := st301o2_p216
  have hstep := st301o2_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p218 : ((3821010291913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 217, stT301o2 (i+1)) + stT301o2 218 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 217
    simpa using h
  have hprev := st301o2_p217
  have hstep := st301o2_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p219 : ((2204334852061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 218, stT301o2 (i+1)) + stT301o2 219 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 218
    simpa using h
  have hprev := st301o2_p218
  have hstep := st301o2_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p220 : ((4651782492527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 219, stT301o2 (i+1)) + stT301o2 220 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 219
    simpa using h
  have hprev := st301o2_p219
  have hstep := st301o2_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p221 : ((35553973823/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 220, stT301o2 (i+1)) + stT301o2 221 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 220
    simpa using h
  have hprev := st301o2_p220
  have hstep := st301o2_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p222 : ((3881993005009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 221, stT301o2 (i+1)) + stT301o2 222 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 221
    simpa using h
  have hprev := st301o2_p221
  have hstep := st301o2_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p223 : ((3215565360809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 222, stT301o2 (i+1)) + stT301o2 223 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 222
    simpa using h
  have hprev := st301o2_p222
  have hstep := st301o2_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p224 : ((2736801616571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 223, stT301o2 (i+1)) + stT301o2 224 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 223
    simpa using h
  have hprev := st301o2_p223
  have hstep := st301o2_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p225 : ((1325707786939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 224, stT301o2 (i+1)) + stT301o2 225 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 224
    simpa using h
  have hprev := st301o2_p224
  have hstep := st301o2_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p226 : ((1496410175119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 225, stT301o2 (i+1)) + stT301o2 226 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 225
    simpa using h
  have hprev := st301o2_p225
  have hstep := st301o2_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p227 : ((451529648137/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 226, stT301o2 (i+1)) + stT301o2 227 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 226
    simpa using h
  have hprev := st301o2_p226
  have hstep := st301o2_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p228 : ((2123005257489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 227, stT301o2 (i+1)) + stT301o2 228 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 227
    simpa using h
  have hprev := st301o2_p227
  have hstep := st301o2_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p229 : ((1157204439163/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 228, stT301o2 (i+1)) + stT301o2 229 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 228
    simpa using h
  have hprev := st301o2_p228
  have hstep := st301o2_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p230 : ((23019162459/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 229, stT301o2 (i+1)) + stT301o2 230 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 229
    simpa using h
  have hprev := st301o2_p229
  have hstep := st301o2_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p231 : ((523074089359/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 230, stT301o2 (i+1)) + stT301o2 231 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 230
    simpa using h
  have hprev := st301o2_p230
  have hstep := st301o2_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p232 : ((3545303554117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 231, stT301o2 (i+1)) + stT301o2 232 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 231
    simpa using h
  have hprev := st301o2_p231
  have hstep := st301o2_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p233 : ((589278728441/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 232, stT301o2 (i+1)) + stT301o2 233 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 232
    simpa using h
  have hprev := st301o2_p232
  have hstep := st301o2_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p234 : ((2627885081701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 233, stT301o2 (i+1)) + stT301o2 234 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 233
    simpa using h
  have hprev := st301o2_p233
  have hstep := st301o2_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p235 : ((2714318541701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 234, stT301o2 (i+1)) + stT301o2 235 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 234
    simpa using h
  have hprev := st301o2_p234
  have hstep := st301o2_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p236 : ((633673781249/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 235, stT301o2 (i+1)) + stT301o2 236 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 235
    simpa using h
  have hprev := st301o2_p235
  have hstep := st301o2_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p237 : ((3809355800617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 236, stT301o2 (i+1)) + stT301o2 237 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 236
    simpa using h
  have hprev := st301o2_p236
  have hstep := st301o2_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p238 : ((4386872263467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 237, stT301o2 (i+1)) + stT301o2 238 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 237
    simpa using h
  have hprev := st301o2_p237
  have hstep := st301o2_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p239 : ((4678929054081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 238, stT301o2 (i+1)) + stT301o2 239 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 238
    simpa using h
  have hprev := st301o2_p238
  have hstep := st301o2_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p240 : ((4576130270091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 239, stT301o2 (i+1)) + stT301o2 240 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 239
    simpa using h
  have hprev := st301o2_p239
  have hstep := st301o2_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p241 : ((2060244518463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 240, stT301o2 (i+1)) + stT301o2 241 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 240
    simpa using h
  have hprev := st301o2_p240
  have hstep := st301o2_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p242 : ((435755327247/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 241, stT301o2 (i+1)) + stT301o2 242 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 241
    simpa using h
  have hprev := st301o2_p241
  have hstep := st301o2_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p243 : ((1455407543143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 242, stT301o2 (i+1)) + stT301o2 243 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 242
    simpa using h
  have hprev := st301o2_p242
  have hstep := st301o2_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p244 : ((2607211831331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 243, stT301o2 (i+1)) + stT301o2 244 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 243
    simpa using h
  have hprev := st301o2_p243
  have hstep := st301o2_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p245 : ((2684605908847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 244, stT301o2 (i+1)) + stT301o2 245 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 244
    simpa using h
  have hprev := st301o2_p244
  have hstep := st301o2_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p246 : ((622380338627/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 245, stT301o2 (i+1)) + stT301o2 246 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 245
    simpa using h
  have hprev := st301o2_p245
  have hstep := st301o2_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p247 : ((3732013262707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 246, stT301o2 (i+1)) + stT301o2 247 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 246
    simpa using h
  have hprev := st301o2_p246
  have hstep := st301o2_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p248 : ((4321125622707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 247, stT301o2 (i+1)) + stT301o2 248 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 247
    simpa using h
  have hprev := st301o2_p247
  have hstep := st301o2_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p249 : ((4669876614387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 248, stT301o2 (i+1)) + stT301o2 249 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 248
    simpa using h
  have hprev := st301o2_p248
  have hstep := st301o2_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p250 : ((4656936564627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 249, stT301o2 (i+1)) + stT301o2 250 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 249
    simpa using h
  have hprev := st301o2_p249
  have hstep := st301o2_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p251 : ((2144769392281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 250, stT301o2 (i+1)) + stT301o2 251 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 250
    simpa using h
  have hprev := st301o2_p250
  have hstep := st301o2_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p252 : ((3698014736447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 251, stT301o2 (i+1)) + stT301o2 252 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 251
    simpa using h
  have hprev := st301o2_p251
  have hstep := st301o2_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p253 : ((1544020193731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 252, stT301o2 (i+1)) + stT301o2 253 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 252
    simpa using h
  have hprev := st301o2_p252
  have hstep := st301o2_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p254 : ((1334263221571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 253, stT301o2 (i+1)) + stT301o2 254 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 253
    simpa using h
  have hprev := st301o2_p253
  have hstep := st301o2_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p255 : ((645139528123/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 254, stT301o2 (i+1)) + stT301o2 255 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 254
    simpa using h
  have hprev := st301o2_p254
  have hstep := st301o2_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p256 : ((712834840623/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 255, stT301o2 (i+1)) + stT301o2 256 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 255
    simpa using h
  have hprev := st301o2_p255
  have hstep := st301o2_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p257 : ((1693820151733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 256, stT301o2 (i+1)) + stT301o2 257 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 256
    simpa using h
  have hprev := st301o2_p256
  have hstep := st301o2_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p258 : ((2004723581239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 257, stT301o2 (i+1)) + stT301o2 258 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 257
    simpa using h
  have hprev := st301o2_p257
  have hstep := st301o2_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p259 : ((902243384293/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 258, stT301o2 (i+1)) + stT301o2 259 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 258
    simpa using h
  have hprev := st301o2_p258
  have hstep := st301o2_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p260 : ((1182422711433/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 259, stT301o2 (i+1)) + stT301o2 260 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 259
    simpa using h
  have hprev := st301o2_p259
  have hstep := st301o2_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p261 : ((4595980800957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 260, stT301o2 (i+1)) + stT301o2 261 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 260
    simpa using h
  have hprev := st301o2_p260
  have hstep := st301o2_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p262 : ((2077849584193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 261, stT301o2 (i+1)) + stT301o2 262 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 261
    simpa using h
  have hprev := st301o2_p261
  have hstep := st301o2_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p263 : ((443982472389/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 262, stT301o2 (i+1)) + stT301o2 263 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 262
    simpa using h
  have hprev := st301o2_p262
  have hstep := st301o2_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p264 : ((1488667022159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 263, stT301o2 (i+1)) + stT301o2 264 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 263
    simpa using h
  have hprev := st301o2_p263
  have hstep := st301o2_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p265 : ((1306483721699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 264, stT301o2 (i+1)) + stT301o2 265 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 264
    simpa using h
  have hprev := st301o2_p264
  have hstep := st301o2_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p266 : ((1285625618609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 265, stT301o2 (i+1)) + stT301o2 266 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 265
    simpa using h
  have hprev := st301o2_p265
  have hstep := st301o2_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p267 : ((44731884447/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 266, stT301o2 (i+1)) + stT301o2 267 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 266
    simpa using h
  have hprev := st301o2_p266
  have hstep := st301o2_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p268 : ((135819014623/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 267, stT301o2 (i+1)) + stT301o2 268 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 267
    simpa using h
  have hprev := st301o2_p267
  have hstep := st301o2_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p269 : ((800884523673/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 268, stT301o2 (i+1)) + stT301o2 269 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 268
    simpa using h
  have hprev := st301o2_p268
  have hstep := st301o2_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p270 : ((900818958609/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 269, stT301o2 (i+1)) + stT301o2 270 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 269
    simpa using h
  have hprev := st301o2_p269
  have hstep := st301o2_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p271 : ((4744499149781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 270, stT301o2 (i+1)) + stT301o2 271 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 270
    simpa using h
  have hprev := st301o2_p270
  have hstep := st301o2_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p272 : ((4655432048161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 271, stT301o2 (i+1)) + stT301o2 272 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 271
    simpa using h
  have hprev := st301o2_p271
  have hstep := st301o2_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p273 : ((170626318137/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 272, stT301o2 (i+1)) + stT301o2 273 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 272
    simpa using h
  have hprev := st301o2_p272
  have hstep := st301o2_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p274 : ((738466628793/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 273, stT301o2 (i+1)) + stT301o2 274 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 273
    simpa using h
  have hprev := st301o2_p273
  have hstep := st301o2_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p275 : ((776201506499/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 274, stT301o2 (i+1)) + stT301o2 275 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 274
    simpa using h
  have hprev := st301o2_p274
  have hstep := st301o2_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p276 : ((1337098370333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 275, stT301o2 (i+1)) + stT301o2 276 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 275
    simpa using h
  have hprev := st301o2_p275
  have hstep := st301o2_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p277 : ((1261948057183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 276, stT301o2 (i+1)) + stT301o2 277 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 276
    simpa using h
  have hprev := st301o2_p276
  have hstep := st301o2_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p278 : ((1347557499703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 277, stT301o2 (i+1)) + stT301o2 278 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 277
    simpa using h
  have hprev := st301o2_p277
  have hstep := st301o2_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p279 : ((1568424899009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 278, stT301o2 (i+1)) + stT301o2 279 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 278
    simpa using h
  have hprev := st301o2_p278
  have hstep := st301o2_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p280 : ((465279651649/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 279, stT301o2 (i+1)) + stT301o2 280 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 279
    simpa using h
  have hprev := st301o2_p279
  have hstep := st301o2_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p281 : ((2142880033727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 280, stT301o2 (i+1)) + stT301o2 281 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 280
    simpa using h
  have hprev := st301o2_p280
  have hstep := st301o2_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p282 : ((934053840329/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 281, stT301o2 (i+1)) + stT301o2 282 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 281
    simpa using h
  have hprev := st301o2_p281
  have hstep := st301o2_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p283 : ((190815140209/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 282, stT301o2 (i+1)) + stT301o2 283 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 282
    simpa using h
  have hprev := st301o2_p282
  have hstep := st301o2_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p284 : ((4560420154477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 283, stT301o2 (i+1)) + stT301o2 284 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 283
    simpa using h
  have hprev := st301o2_p283
  have hstep := st301o2_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p285 : ((2049934699663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 284, stT301o2 (i+1)) + stT301o2 285 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 284
    simpa using h
  have hprev := st301o2_p284
  have hstep := st301o2_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p286 : ((175771905001/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 285, stT301o2 (i+1)) + stT301o2 286 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 285
    simpa using h
  have hprev := st301o2_p285
  have hstep := st301o2_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p287 : ((741389340307/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 286, stT301o2 (i+1)) + stT301o2 287 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 286
    simpa using h
  have hprev := st301o2_p286
  have hstep := st301o2_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p288 : ((649318679563/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 287, stT301o2 (i+1)) + stT301o2 288 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 287
    simpa using h
  have hprev := st301o2_p287
  have hstep := st301o2_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p289 : ((78355107309/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 288, stT301o2 (i+1)) + stT301o2 289 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 288
    simpa using h
  have hprev := st301o2_p288
  have hstep := st301o2_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p290 : ((339718636521/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 289, stT301o2 (i+1)) + stT301o2 290 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 289
    simpa using h
  have hprev := st301o2_p289
  have hstep := st301o2_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p291 : ((1585612660249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 290, stT301o2 (i+1)) + stT301o2 291 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 290
    simpa using h
  have hprev := st301o2_p290
  have hstep := st301o2_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p292 : ((3747970011813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 291, stT301o2 (i+1)) + stT301o2 292 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 291
    simpa using h
  have hprev := st301o2_p291
  have hstep := st301o2_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p293 : ((4297806004421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 292, stT301o2 (i+1)) + stT301o2 293 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 292
    simpa using h
  have hprev := st301o2_p292
  have hstep := st301o2_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p294 : ((1169864383297/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 293, stT301o2 (i+1)) + stT301o2 294 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 293
    simpa using h
  have hprev := st301o2_p293
  have hstep := st301o2_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p295 : ((1199118709909/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 294, stT301o2 (i+1)) + stT301o2 295 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 294
    simpa using h
  have hprev := st301o2_p294
  have hstep := st301o2_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p296 : ((184834162281/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 295, stT301o2 (i+1)) + stT301o2 296 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 295
    simpa using h
  have hprev := st301o2_p295
  have hstep := st301o2_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p297 : ((4198760894727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 296, stT301o2 (i+1)) + stT301o2 297 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 296
    simpa using h
  have hprev := st301o2_p296
  have hstep := st301o2_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p298 : ((909379431513/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 297, stT301o2 (i+1)) + stT301o2 298 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 297
    simpa using h
  have hprev := st301o2_p297
  have hstep := st301o2_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p299 : ((3077693191547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 298, stT301o2 (i+1)) + stT301o2 299 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 298
    simpa using h
  have hprev := st301o2_p298
  have hstep := st301o2_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p300 : ((2657694587789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 299, stT301o2 (i+1)) + stT301o2 300 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 299
    simpa using h
  have hprev := st301o2_p299
  have hstep := st301o2_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p301 : ((1239900652143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 300, stT301o2 (i+1)) + stT301o2 301 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 300
    simpa using h
  have hprev := st301o2_p300
  have hstep := st301o2_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p302 : ((1292945401313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 301, stT301o2 (i+1)) + stT301o2 302 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 301
    simpa using h
  have hprev := st301o2_p301
  have hstep := st301o2_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p303 : ((1474215784737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 302, stT301o2 (i+1)) + stT301o2 303 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 302
    simpa using h
  have hprev := st301o2_p302
  have hstep := st301o2_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p304 : ((695691118401/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 303, stT301o2 (i+1)) + stT301o2 304 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 303
    simpa using h
  have hprev := st301o2_p303
  have hstep := st301o2_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p305 : ((4048029701967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 304, stT301o2 (i+1)) + stT301o2 305 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 304
    simpa using h
  have hprev := st301o2_p304
  have hstep := st301o2_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p306 : ((4521430179321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 305, stT301o2 (i+1)) + stT301o2 306 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 305
    simpa using h
  have hprev := st301o2_p305
  have hstep := st301o2_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p307 : ((4787380656911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 306, stT301o2 (i+1)) + stT301o2 307 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 306
    simpa using h
  have hprev := st301o2_p306
  have hstep := st301o2_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p308 : ((4784717397689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 307, stT301o2 (i+1)) + stT301o2 308 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 307
    simpa using h
  have hprev := st301o2_p307
  have hstep := st301o2_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p309 : ((903143948263/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 308, stT301o2 (i+1)) + stT301o2 309 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 308
    simpa using h
  have hprev := st301o2_p308
  have hstep := st301o2_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p310 : ((4044401019311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 309, stT301o2 (i+1)) + stT301o2 310 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 309
    simpa using h
  have hprev := st301o2_p309
  have hstep := st301o2_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p311 : ((3480588595199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 310, stT301o2 (i+1)) + stT301o2 311 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 310
    simpa using h
  have hprev := st301o2_p310
  have hstep := st301o2_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p312 : ((2953927599947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 311, stT301o2 (i+1)) + stT301o2 312 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 311
    simpa using h
  have hprev := st301o2_p311
  have hstep := st301o2_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p313 : ((2584002295371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 312, stT301o2 (i+1)) + stT301o2 313 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 312
    simpa using h
  have hprev := st301o2_p312
  have hstep := st301o2_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p314 : ((2453483359131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 313, stT301o2 (i+1)) + stT301o2 314 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 313
    simpa using h
  have hprev := st301o2_p313
  have hstep := st301o2_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p315 : ((2590230966639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 314, stT301o2 (i+1)) + stT301o2 315 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 314
    simpa using h
  have hprev := st301o2_p314
  have hstep := st301o2_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p316 : ((2962076389983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 315, stT301o2 (i+1)) + stT301o2 316 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 315
    simpa using h
  have hprev := st301o2_p315
  have hstep := st301o2_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p317 : ((1742534934029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 316, stT301o2 (i+1)) + stT301o2 317 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 316
    simpa using h
  have hprev := st301o2_p316
  have hstep := st301o2_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p318 : ((2021479469603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 317, stT301o2 (i+1)) + stT301o2 318 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 317
    simpa using h
  have hprev := st301o2_p317
  have hstep := st301o2_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p319 : ((451324694331/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 318, stT301o2 (i+1)) + stT301o2 319 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 318
    simpa using h
  have hprev := st301o2_p318
  have hstep := st301o2_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p320 : ((2397009718751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 319, stT301o2 (i+1)) + stT301o2 320 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 319
    simpa using h
  have hprev := st301o2_p319
  have hstep := st301o2_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p321 : ((2412805222251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 320, stT301o2 (i+1)) + stT301o2 321 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 320
    simpa using h
  have hprev := st301o2_p320
  have hstep := st301o2_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p322 : ((4602712776477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 321, stT301o2 (i+1)) + stT301o2 322 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 321
    simpa using h
  have hprev := st301o2_p321
  have hstep := st301o2_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p323 : ((4174506920777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 322, stT301o2 (i+1)) + stT301o2 323 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 322
    simpa using h
  have hprev := st301o2_p322
  have hstep := st301o2_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p324 : ((3633233709981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 323, stT301o2 (i+1)) + stT301o2 324 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 323
    simpa using h
  have hprev := st301o2_p323
  have hstep := st301o2_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p325 : ((193370111239/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 324, stT301o2 (i+1)) + stT301o2 325 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 324
    simpa using h
  have hprev := st301o2_p324
  have hstep := st301o2_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p326 : ((533963378543/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 325, stT301o2 (i+1)) + stT301o2 326 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 325
    simpa using h
  have hprev := st301o2_p325
  have hstep := st301o2_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p327 : ((2448767615263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 326, stT301o2 (i+1)) + stT301o2 327 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 326
    simpa using h
  have hprev := st301o2_p326
  have hstep := st301o2_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p328 : ((1237723644673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 327, stT301o2 (i+1)) + stT301o2 328 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 327
    simpa using h
  have hprev := st301o2_p327
  have hstep := st301o2_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p329 : ((274288675551/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 328, stT301o2 (i+1)) + stT301o2 329 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 328
    simpa using h
  have hprev := st301o2_p328
  have hstep := st301o2_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p330 : ((3194841014687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 329, stT301o2 (i+1)) + stT301o2 330 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 329
    simpa using h
  have hprev := st301o2_p329
  have hstep := st301o2_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p331 : ((186905621867/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 330, stT301o2 (i+1)) + stT301o2 331 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 330
    simpa using h
  have hprev := st301o2_p330
  have hstep := st301o2_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p332 : ((4262093250059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 331, stT301o2 (i+1)) + stT301o2 332 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 331
    simpa using h
  have hprev := st301o2_p331
  have hstep := st301o2_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p333 : ((932270544747/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 332, stT301o2 (i+1)) + stT301o2 333 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 332
    simpa using h
  have hprev := st301o2_p332
  have hstep := st301o2_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p334 : ((971332492517/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 333, stT301o2 (i+1)) + stT301o2 334 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 333
    simpa using h
  have hprev := st301o2_p333
  have hstep := st301o2_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p335 : ((2405155502051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 334, stT301o2 (i+1)) + stT301o2 335 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 334
    simpa using h
  have hprev := st301o2_p334
  have hstep := st301o2_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p336 : ((4532861546817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 335, stT301o2 (i+1)) + stT301o2 336 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 335
    simpa using h
  have hprev := st301o2_p335
  have hstep := st301o2_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p337 : ((510026681729/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 336, stT301o2 (i+1)) + stT301o2 337 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 336
    simpa using h
  have hprev := st301o2_p336
  have hstep := st301o2_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p338 : ((354189888897/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 337, stT301o2 (i+1)) + stT301o2 338 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 337
    simpa using h
  have hprev := st301o2_p337
  have hstep := st301o2_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p339 : ((1511539431861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 338, stT301o2 (i+1)) + stT301o2 339 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 338
    simpa using h
  have hprev := st301o2_p338
  have hstep := st301o2_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p340 : ((2623939749897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 339, stT301o2 (i+1)) + stT301o2 340 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 339
    simpa using h
  have hprev := st301o2_p339
  have hstep := st301o2_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p341 : ((1210257085639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 340, stT301o2 (i+1)) + stT301o2 341 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 340
    simpa using h
  have hprev := st301o2_p340
  have hstep := st301o2_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p342 : ((1225286357611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 341, stT301o2 (i+1)) + stT301o2 342 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 341
    simpa using h
  have hprev := st301o2_p341
  have hstep := st301o2_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p343 : ((2707077107519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 342, stT301o2 (i+1)) + stT301o2 343 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 342
    simpa using h
  have hprev := st301o2_p342
  have hstep := st301o2_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p344 : ((1570144323613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 343, stT301o2 (i+1)) + stT301o2 344 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 343
    simpa using h
  have hprev := st301o2_p343
  have hstep := st301o2_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p345 : ((1833917633991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 344, stT301o2 (i+1)) + stT301o2 345 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 344
    simpa using h
  have hprev := st301o2_p344
  have hstep := st301o2_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p346 : ((838129869411/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 345, stT301o2 (i+1)) + stT301o2 346 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 345
    simpa using h
  have hprev := st301o2_p345
  have hstep := st301o2_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p347 : ((4611657779711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 346, stT301o2 (i+1)) + stT301o2 347 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 346
    simpa using h
  have hprev := st301o2_p346
  have hstep := st301o2_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p348 : ((4853674734423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 347, stT301o2 (i+1)) + stT301o2 348 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 347
    simpa using h
  have hprev := st301o2_p347
  have hstep := st301o2_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p349 : ((4873243756569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 348, stT301o2 (i+1)) + stT301o2 349 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 348
    simpa using h
  have hprev := st301o2_p348
  have hstep := st301o2_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p350 : ((4668024341179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 349, stT301o2 (i+1)) + stT301o2 350 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 349
    simpa using h
  have hprev := st301o2_p349
  have hstep := st301o2_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p351 : ((4276509580157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 350, stT301o2 (i+1)) + stT301o2 351 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 350
    simpa using h
  have hprev := st301o2_p350
  have hstep := st301o2_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p352 : ((3770413521117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 351, stT301o2 (i+1)) + stT301o2 352 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 351
    simpa using h
  have hprev := st301o2_p351
  have hstep := st301o2_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p353 : ((648244749577/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 352, stT301o2 (i+1)) + stT301o2 353 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 352
    simpa using h
  have hprev := st301o2_p352
  have hstep := st301o2_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p354 : ((111341966057/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 353, stT301o2 (i+1)) + stT301o2 354 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 353
    simpa using h
  have hprev := st301o2_p353
  have hstep := st301o2_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p355 : ((247825242029/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 354, stT301o2 (i+1)) + stT301o2 355 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 354
    simpa using h
  have hprev := st301o2_p354
  have hstep := st301o2_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p356 : ((594603067167/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 355, stT301o2 (i+1)) + stT301o2 356 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 355
    simpa using h
  have hprev := st301o2_p355
  have hstep := st301o2_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p357 : ((625107927553/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 356, stT301o2 (i+1)) + stT301o2 357 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 356
    simpa using h
  have hprev := st301o2_p356
  have hstep := st301o2_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p358 : ((88181203331/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 357, stT301o2 (i+1)) + stT301o2 358 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 357
    simpa using h
  have hprev := st301o2_p357
  have hstep := st301o2_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p359 : ((1642809040349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 358, stT301o2 (i+1)) + stT301o2 359 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 358
    simpa using h
  have hprev := st301o2_p358
  have hstep := st301o2_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p360 : ((47637594689/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 359, stT301o2 (i+1)) + stT301o2 360 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 359
    simpa using h
  have hprev := st301o2_p359
  have hstep := st301o2_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p361 : ((861475576639/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 360, stT301o2 (i+1)) + stT301o2 361 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 360
    simpa using h
  have hprev := st301o2_p360
  have hstep := st301o2_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p362 : ((187603076063/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 361, stT301o2 (i+1)) + stT301o2 362 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 361
    simpa using h
  have hprev := st301o2_p361
  have hstep := st301o2_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p363 : ((2447341860001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 362, stT301o2 (i+1)) + stT301o2 363 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 362
    simpa using h
  have hprev := st301o2_p362
  have hstep := st301o2_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p364 : ((122189225073/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 363, stT301o2 (i+1)) + stT301o2 364 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 363
    simpa using h
  have hprev := st301o2_p363
  have hstep := st301o2_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p365 : ((583880786317/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 364, stT301o2 (i+1)) + stT301o2 365 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 364
    simpa using h
  have hprev := st301o2_p364
  have hstep := st301o2_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p366 : ((214121025619/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 365, stT301o2 (i+1)) + stT301o2 366 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 365
    simpa using h
  have hprev := st301o2_p365
  have hstep := st301o2_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p367 : ((47340264713/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 366, stT301o2 (i+1)) + stT301o2 367 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 366
    simpa using h
  have hprev := st301o2_p366
  have hstep := st301o2_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p368 : ((3267905163187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 367, stT301o2 (i+1)) + stT301o2 368 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 367
    simpa using h
  have hprev := st301o2_p367
  have hstep := st301o2_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p369 : ((2810024859547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 368, stT301o2 (i+1)) + stT301o2 369 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 368
    simpa using h
  have hprev := st301o2_p368
  have hstep := st301o2_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p370 : ((2488177426087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 369, stT301o2 (i+1)) + stT301o2 370 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 369
    simpa using h
  have hprev := st301o2_p369
  have hstep := st301o2_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p371 : ((2354022606087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 370, stT301o2 (i+1)) + stT301o2 371 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 370
    simpa using h
  have hprev := st301o2_p370
  have hstep := st301o2_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p372 : ((1214148889581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 371, stT301o2 (i+1)) + stT301o2 372 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 371
    simpa using h
  have hprev := st301o2_p371
  have hstep := st301o2_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p373 : ((1348976212681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 372, stT301o2 (i+1)) + stT301o2 373 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 372
    simpa using h
  have hprev := st301o2_p372
  have hstep := st301o2_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p374 : ((1559382015503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 373, stT301o2 (i+1)) + stT301o2 374 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 373
    simpa using h
  have hprev := st301o2_p373
  have hstep := st301o2_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p375 : ((226431037641/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 374, stT301o2 (i+1)) + stT301o2 375 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 374
    simpa using h
  have hprev := st301o2_p374
  have hstep := st301o2_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p376 : ((516250312077/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 375, stT301o2 (i+1)) + stT301o2 376 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 375
    simpa using h
  have hprev := st301o2_p375
  have hstep := st301o2_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p377 : ((285006551839/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 376, stT301o2 (i+1)) + stT301o2 377 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 376
    simpa using h
  have hprev := st301o2_p376
  have hstep := st301o2_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p378 : ((302883220489/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 377, stT301o2 (i+1)) + stT301o2 378 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 377
    simpa using h
  have hprev := st301o2_p377
  have hstep := st301o2_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p379 : ((309011243939/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 378, stT301o2 (i+1)) + stT301o2 379 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 378
    simpa using h
  have hprev := st301o2_p378
  have hstep := st301o2_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p380 : ((2419999151447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 379, stT301o2 (i+1)) + stT301o2 380 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 379
    simpa using h
  have hprev := st301o2_p379
  have hstep := st301o2_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p381 : ((2275351339691/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 380, stT301o2 (i+1)) + stT301o2 381 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 380
    simpa using h
  have hprev := st301o2_p380
  have hstep := st301o2_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p382 : ((4121671462597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 381, stT301o2 (i+1)) + stT301o2 382 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 381
    simpa using h
  have hprev := st301o2_p381
  have hstep := st301o2_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p383 : ((1809593705657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 382, stT301o2 (i+1)) + stT301o2 383 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 382
    simpa using h
  have hprev := st301o2_p382
  have hstep := st301o2_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p384 : ((390002317711/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 383, stT301o2 (i+1)) + stT301o2 384 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 383
    simpa using h
  have hprev := st301o2_p383
  have hstep := st301o2_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p385 : ((337456780733/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 384, stT301o2 (i+1)) + stT301o2 385 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 384
    simpa using h
  have hprev := st301o2_p384
  have hstep := st301o2_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p386 : ((2420952815157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 385, stT301o2 (i+1)) + stT301o2 386 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 385
    simpa using h
  have hprev := st301o2_p385
  have hstep := st301o2_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p387 : ((1162462954377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 386, stT301o2 (i+1)) + stT301o2 387 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 386
    simpa using h
  have hprev := st301o2_p386
  have hstep := st301o2_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p388 : ((2424962365731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 387, stT301o2 (i+1)) + stT301o2 388 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 387
    simpa using h
  have hprev := st301o2_p387
  have hstep := st301o2_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p389 : ((2705244542791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 388, stT301o2 (i+1)) + stT301o2 389 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 388
    simpa using h
  have hprev := st301o2_p388
  have hstep := st301o2_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p390 : ((390442281347/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 389, stT301o2 (i+1)) + stT301o2 390 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 389
    simpa using h
  have hprev := st301o2_p389
  have hstep := st301o2_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p391 : ((3617781912681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 390, stT301o2 (i+1)) + stT301o2 391 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 390
    simpa using h
  have hprev := st301o2_p390
  have hstep := st301o2_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p392 : ((4115448447761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 391, stT301o2 (i+1)) + stT301o2 392 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 391
    simpa using h
  have hprev := st301o2_p391
  have hstep := st301o2_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p393 : ((4544234657349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 392, stT301o2 (i+1)) + stT301o2 393 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 392
    simpa using h
  have hprev := st301o2_p392
  have hstep := st301o2_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p394 : ((4842512771621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 393, stT301o2 (i+1)) + stT301o2 394 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 393
    simpa using h
  have hprev := st301o2_p393
  have hstep := st301o2_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p395 : ((4968039631541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 394, stT301o2 (i+1)) + stT301o2 395 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 394
    simpa using h
  have hprev := st301o2_p394
  have hstep := st301o2_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p396 : ((4903696093743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 395, stT301o2 (i+1)) + stT301o2 396 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 395
    simpa using h
  have hprev := st301o2_p395
  have hstep := st301o2_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p397 : ((931915949423/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 396, stT301o2 (i+1)) + stT301o2 397 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 396
    simpa using h
  have hprev := st301o2_p396
  have hstep := st301o2_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p398 : ((427113970369/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 397, stT301o2 (i+1)) + stT301o2 398 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 397
    simpa using h
  have hprev := st301o2_p397
  have hstep := st301o2_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p399 : ((1896916955929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 398, stT301o2 (i+1)) + stT301o2 399 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 398
    simpa using h
  have hprev := st301o2_p398
  have hstep := st301o2_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p400 : ((659007282853/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 399, stT301o2 (i+1)) + stT301o2 400 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 399
    simpa using h
  have hprev := st301o2_p399
  have hstep := st301o2_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p401 : ((2844462529721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 400, stT301o2 (i+1)) + stT301o2 401 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 400
    simpa using h
  have hprev := st301o2_p400
  have hstep := st301o2_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p402 : ((2504445286061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 401, stT301o2 (i+1)) + stT301o2 402 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 401
    simpa using h
  have hprev := st301o2_p401
  have hstep := st301o2_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p403 : ((2321437591701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 402, stT301o2 (i+1)) + stT301o2 403 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 402
    simpa using h
  have hprev := st301o2_p402
  have hstep := st301o2_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p404 : ((2319841550749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 403, stT301o2 (i+1)) + stT301o2 404 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 403
    simpa using h
  have hprev := st301o2_p403
  have hstep := st301o2_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p405 : ((249899843669/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 404, stT301o2 (i+1)) + stT301o2 405 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 404
    simpa using h
  have hprev := st301o2_p404
  have hstep := st301o2_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p406 : ((283363753217/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 405, stT301o2 (i+1)) + stT301o2 406 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 405
    simpa using h
  have hprev := st301o2_p405
  have hstep := st301o2_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p407 : ((1638828337813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 406, stT301o2 (i+1)) + stT301o2 407 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 406
    simpa using h
  have hprev := st301o2_p406
  have hstep := st301o2_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p408 : ((1885324194367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 407, stT301o2 (i+1)) + stT301o2 408 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 407
    simpa using h
  have hprev := st301o2_p407
  have hstep := st301o2_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p409 : ((2123104955143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 408, stT301o2 (i+1)) + stT301o2 409 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 408
    simpa using h
  have hprev := st301o2_p408
  have hstep := st301o2_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p410 : ((2320451281019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 409, stT301o2 (i+1)) + stT301o2 410 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 409
    simpa using h
  have hprev := st301o2_p409
  have hstep := st301o2_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p411 : ((980528442893/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 410, stT301o2 (i+1)) + stT301o2 411 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 410
    simpa using h
  have hprev := st301o2_p410
  have hstep := st301o2_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p412 : ((4997437172697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 411, stT301o2 (i+1)) + stT301o2 412 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 411
    simpa using h
  have hprev := st301o2_p411
  have hstep := st301o2_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p413 : ((4913595674449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 412, stT301o2 (i+1)) + stT301o2 413 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 412
    simpa using h
  have hprev := st301o2_p412
  have hstep := st301o2_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p414 : ((4662938036761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 413, stT301o2 (i+1)) + stT301o2 414 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 413
    simpa using h
  have hprev := st301o2_p413
  have hstep := st301o2_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p415 : ((2139466069481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 414, stT301o2 (i+1)) + stT301o2 415 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 414
    simpa using h
  have hprev := st301o2_p414
  have hstep := st301o2_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p416 : ((1906019893323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 415, stT301o2 (i+1)) + stT301o2 416 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 415
    simpa using h
  have hprev := st301o2_p415
  have hstep := st301o2_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p417 : ((830737228849/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 416, stT301o2 (i+1)) + stT301o2 417 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 416
    simpa using h
  have hprev := st301o2_p416
  have hstep := st301o2_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p418 : ((2874634483/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 417, stT301o2 (i+1)) + stT301o2 418 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 417
    simpa using h
  have hprev := st301o2_p417
  have hstep := st301o2_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p419 : ((631065199549/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 418, stT301o2 (i+1)) + stT301o2 419 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 418
    simpa using h
  have hprev := st301o2_p418
  have hstep := st301o2_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p420 : ((1157992384629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 419, stT301o2 (i+1)) + stT301o2 420 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 419
    simpa using h
  have hprev := st301o2_p419
  have hstep := st301o2_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p421 : ((2275538337339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 420, stT301o2 (i+1)) + stT301o2 421 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 420
    simpa using h
  have hprev := st301o2_p420
  have hstep := st301o2_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p422 : ((2407244780859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 421, stT301o2 (i+1)) + stT301o2 422 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 421
    simpa using h
  have hprev := st301o2_p421
  have hstep := st301o2_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p423 : ((538752526311/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 422, stT301o2 (i+1)) + stT301o2 423 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 422
    simpa using h
  have hprev := st301o2_p422
  have hstep := st301o2_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p424 : ((3098572920149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 423, stT301o2 (i+1)) + stT301o2 424 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 423
    simpa using h
  have hprev := st301o2_p423
  have hstep := st301o2_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p425 : ((714154609247/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 424, stT301o2 (i+1)) + stT301o2 425 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 424
    simpa using h
  have hprev := st301o2_p424
  have hstep := st301o2_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p426 : ((1012896627281/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 425, stT301o2 (i+1)) + stT301o2 426 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 425
    simpa using h
  have hprev := st301o2_p425
  have hstep := st301o2_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p427 : ((4481715354251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 426, stT301o2 (i+1)) + stT301o2 427 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 426
    simpa using h
  have hprev := st301o2_p426
  have hstep := st301o2_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p428 : ((4808631633691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 427, stT301o2 (i+1)) + stT301o2 428 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 427
    simpa using h
  have hprev := st301o2_p427
  have hstep := st301o2_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p429 : ((4992878330563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 428, stT301o2 (i+1)) + stT301o2 429 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 428
    simpa using h
  have hprev := st301o2_p428
  have hstep := st301o2_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p430 : ((5012712461781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 429, stT301o2 (i+1)) + stT301o2 430 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 429
    simpa using h
  have hprev := st301o2_p429
  have hstep := st301o2_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p431 : ((4866485241481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 430, stT301o2 (i+1)) + stT301o2 431 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 430
    simpa using h
  have hprev := st301o2_p430
  have hstep := st301o2_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p432 : ((4572549972049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 431, stT301o2 (i+1)) + stT301o2 432 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 431
    simpa using h
  have hprev := st301o2_p431
  have hstep := st301o2_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p433 : ((4166805682189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 432, stT301o2 (i+1)) + stT301o2 433 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 432
    simpa using h
  have hprev := st301o2_p432
  have hstep := st301o2_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p434 : ((3698174701677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 433, stT301o2 (i+1)) + stT301o2 434 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 433
    simpa using h
  have hprev := st301o2_p433
  have hstep := st301o2_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p435 : ((3222603949357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 434, stT301o2 (i+1)) + stT301o2 435 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 434
    simpa using h
  have hprev := st301o2_p434
  have hstep := st301o2_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p436 : ((2796355164109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 435, stT301o2 (i+1)) + stT301o2 436 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 435
    simpa using h
  have hprev := st301o2_p435
  have hstep := st301o2_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p437 : ((2469376422199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 436, stT301o2 (i+1)) + stT301o2 437 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 436
    simpa using h
  have hprev := st301o2_p436
  have hstep := st301o2_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p438 : ((2279541800413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 437, stT301o2 (i+1)) + stT301o2 438 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 437
    simpa using h
  have hprev := st301o2_p437
  have hstep := st301o2_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p439 : ((2248375808213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 438, stT301o2 (i+1)) + stT301o2 439 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 438
    simpa using h
  have hprev := st301o2_p438
  have hstep := st301o2_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p440 : ((95151461069/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 439, stT301o2 (i+1)) + stT301o2 440 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 439
    simpa using h
  have hprev := st301o2_p439
  have hstep := st301o2_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p441 : ((530995059631/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 440, stT301o2 (i+1)) + stT301o2 441 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 440
    simpa using h
  have hprev := st301o2_p440
  have hstep := st301o2_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p442 : ((3044510635907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 441, stT301o2 (i+1)) + stT301o2 442 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 441
    simpa using h
  have hprev := st301o2_p441
  have hstep := st301o2_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p443 : ((3502259219207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 442, stT301o2 (i+1)) + stT301o2 443 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 442
    simpa using h
  have hprev := st301o2_p442
  have hstep := st301o2_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p444 : ((795141165051/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 443, stT301o2 (i+1)) + stT301o2 444 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 443
    simpa using h
  have hprev := st301o2_p443
  have hstep := st301o2_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p445 : ((176440778103/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 444, stT301o2 (i+1)) + stT301o2 445 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 444
    simpa using h
  have hprev := st301o2_p444
  have hstep := st301o2_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p446 : ((1189788091461/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 445, stT301o2 (i+1)) + stT301o2 446 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 445
    simpa using h
  have hprev := st301o2_p445
  have hstep := st301o2_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p447 : ((1245326701287/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 446, stT301o2 (i+1)) + stT301o2 447 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 446
    simpa using h
  have hprev := st301o2_p446
  have hstep := st301o2_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p448 : ((2526567069399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 447, stT301o2 (i+1)) + stT301o2 448 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 447
    simpa using h
  have hprev := st301o2_p447
  have hstep := st301o2_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p449 : ((310455187053/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 448, stT301o2 (i+1)) + stT301o2 449 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 448
    simpa using h
  have hprev := st301o2_p448
  have hstep := st301o2_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p450 : ((4733969101983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 449, stT301o2 (i+1)) + stT301o2 450 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 449
    simpa using h
  have hprev := st301o2_p449
  have hstep := st301o2_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p451 : ((875925702691/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 450, stT301o2 (i+1)) + stT301o2 451 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 450
    simpa using h
  have hprev := st301o2_p450
  have hstep := st301o2_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p452 : ((1971898592413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 451, stT301o2 (i+1)) + stT301o2 452 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 451
    simpa using h
  have hprev := st301o2_p451
  have hstep := st301o2_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p453 : ((694918939749/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 452, stT301o2 (i+1)) + stT301o2 453 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 452
    simpa using h
  have hprev := st301o2_p452
  have hstep := st301o2_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p454 : ((604673097113/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 453, stT301o2 (i+1)) + stT301o2 454 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 453
    simpa using h
  have hprev := st301o2_p453
  have hstep := st301o2_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p455 : ((2639061533989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 454, stT301o2 (i+1)) + stT301o2 455 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 454
    simpa using h
  have hprev := st301o2_p454
  have hstep := st301o2_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p456 : ((472593256727/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 455, stT301o2 (i+1)) + stT301o2 456 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 455
    simpa using h
  have hprev := st301o2_p455
  have hstep := st301o2_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p457 : ((556086132469/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 456, stT301o2 (i+1)) + stT301o2 457 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 456
    simpa using h
  have hprev := st301o2_p456
  have hstep := st301o2_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p458 : ((2237477125121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 457, stT301o2 (i+1)) + stT301o2 458 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 457
    simpa using h
  have hprev := st301o2_p457
  have hstep := st301o2_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p459 : ((2400313819281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 458, stT301o2 (i+1)) + stT301o2 459 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 458
    simpa using h
  have hprev := st301o2_p458
  have hstep := st301o2_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p460 : ((2694889967873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 459, stT301o2 (i+1)) + stT301o2 460 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 459
    simpa using h
  have hprev := st301o2_p459
  have hstep := st301o2_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p461 : ((3089462992883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 460, stT301o2 (i+1)) + stT301o2 461 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 460
    simpa using h
  have hprev := st301o2_p460
  have hstep := st301o2_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p462 : ((3542009469187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 461, stT301o2 (i+1)) + stT301o2 462 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 461
    simpa using h
  have hprev := st301o2_p461
  have hstep := st301o2_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p463 : ((2002391079239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 462, stT301o2 (i+1)) + stT301o2 463 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 462
    simpa using h
  have hprev := st301o2_p462
  have hstep := st301o2_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p464 : ((2214684795449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 463, stT301o2 (i+1)) + stT301o2 464 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 463
    simpa using h
  have hprev := st301o2_p463
  have hstep := st301o2_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p465 : ((2385871359459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 464, stT301o2 (i+1)) + stT301o2 465 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 464
    simpa using h
  have hprev := st301o2_p464
  have hstep := st301o2_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p466 : ((156149103109/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 465, stT301o2 (i+1)) + stT301o2 466 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 465
    simpa using h
  have hprev := st301o2_p465
  have hstep := st301o2_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p467 : ((635215866649/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 466, stT301o2 (i+1)) + stT301o2 467 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 466
    simpa using h
  have hprev := st301o2_p466
  have hstep := st301o2_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p468 : ((2509233941921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 467, stT301o2 (i+1)) + stT301o2 468 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 467
    simpa using h
  have hprev := st301o2_p467
  have hstep := st301o2_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p469 : ((240704020103/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 468, stT301o2 (i+1)) + stT301o2 469 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 468
    simpa using h
  have hprev := st301o2_p468
  have hstep := st301o2_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p470 : ((561247403427/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 469, stT301o2 (i+1)) + stT301o2 470 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 469
    simpa using h
  have hprev := st301o2_p469
  have hstep := st301o2_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p471 : ((101988506019/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 470, stT301o2 (i+1)) + stT301o2 471 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 470
    simpa using h
  have hprev := st301o2_p470
  have hstep := st301o2_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p472 : ((453073199727/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 471, stT301o2 (i+1)) + stT301o2 472 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 471
    simpa using h
  have hprev := st301o2_p471
  have hstep := st301o2_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p473 : ((3171067778481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 472, stT301o2 (i+1)) + stT301o2 473 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 472
    simpa using h
  have hprev := st301o2_p472
  have hstep := st301o2_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p474 : ((2764414654461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 473, stT301o2 (i+1)) + stT301o2 474 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 473
    simpa using h
  have hprev := st301o2_p473
  have hstep := st301o2_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p475 : ((2444999216493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 474, stT301o2 (i+1)) + stT301o2 475 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 474
    simpa using h
  have hprev := st301o2_p474
  have hstep := st301o2_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p476 : ((2244188289543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 475, stT301o2 (i+1)) + stT301o2 476 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 475
    simpa using h
  have hprev := st301o2_p475
  have hstep := st301o2_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p477 : ((1090678608009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 476, stT301o2 (i+1)) + stT301o2 477 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 476
    simpa using h
  have hprev := st301o2_p476
  have hstep := st301o2_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p478 : ((565533257049/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 477, stT301o2 (i+1)) + stT301o2 478 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 477
    simpa using h
  have hprev := st301o2_p477
  have hstep := st301o2_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p479 : ((2477990121193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 478, stT301o2 (i+1)) + stT301o2 479 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 478
    simpa using h
  have hprev := st301o2_p478
  have hstep := st301o2_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p480 : ((350911271591/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 479, stT301o2 (i+1)) + stT301o2 480 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 479
    simpa using h
  have hprev := st301o2_p479
  have hstep := st301o2_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p481 : ((402189445111/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 480, stT301o2 (i+1)) + stT301o2 481 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 480
    simpa using h
  have hprev := st301o2_p480
  have hstep := st301o2_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p482 : ((917146084247/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 481, stT301o2 (i+1)) + stT301o2 482 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 481
    simpa using h
  have hprev := st301o2_p481
  have hstep := st301o2_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p483 : ((514599266581/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 482, stT301o2 (i+1)) + stT301o2 483 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 482
    simpa using h
  have hprev := st301o2_p482
  have hstep := st301o2_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p484 : ((4519075094003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 483, stT301o2 (i+1)) + stT301o2 484 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 483
    simpa using h
  have hprev := st301o2_p483
  have hstep := st301o2_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p485 : ((4837109016251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 484, stT301o2 (i+1)) + stT301o2 485 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 484
    simpa using h
  have hprev := st301o2_p484
  have hstep := st301o2_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p486 : ((1260227637563/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 485, stT301o2 (i+1)) + stT301o2 486 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 485
    simpa using h
  have hprev := st301o2_p485
  have hstep := st301o2_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p487 : ((2555796350839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 486, stT301o2 (i+1)) + stT301o2 487 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 486
    simpa using h
  have hprev := st301o2_p486
  have hstep := st301o2_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p488 : ((5043005948351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 487, stT301o2 (i+1)) + stT301o2 488 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 487
    simpa using h
  have hprev := st301o2_p487
  have hstep := st301o2_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p489 : ((4842173657239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 488, stT301o2 (i+1)) + stT301o2 489 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 488
    simpa using h
  have hprev := st301o2_p488
  have hstep := st301o2_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p490 : ((4528455350709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 489, stT301o2 (i+1)) + stT301o2 490 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 489
    simpa using h
  have hprev := st301o2_p489
  have hstep := st301o2_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p491 : ((4131604104987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 490, stT301o2 (i+1)) + stT301o2 491 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 490
    simpa using h
  have hprev := st301o2_p490
  have hstep := st301o2_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p492 : ((3688874216617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 491, stT301o2 (i+1)) + stT301o2 492 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 491
    simpa using h
  have hprev := st301o2_p491
  have hstep := st301o2_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p493 : ((3241469612173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 492, stT301o2 (i+1)) + stT301o2 493 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 492
    simpa using h
  have hprev := st301o2_p492
  have hstep := st301o2_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p494 : ((2830697575003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 493, stT301o2 (i+1)) + stT301o2 494 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 493
    simpa using h
  have hprev := st301o2_p493
  have hstep := st301o2_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p495 : ((2494165451291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 494, stT301o2 (i+1)) + stT301o2 495 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 494
    simpa using h
  have hprev := st301o2_p494
  have hstep := st301o2_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p496 : ((2262388465617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 495, stT301o2 (i+1)) + stT301o2 496 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 495
    simpa using h
  have hprev := st301o2_p495
  have hstep := st301o2_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p497 : ((2156082860113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 496, stT301o2 (i+1)) + stT301o2 497 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 496
    simpa using h
  have hprev := st301o2_p496
  have hstep := st301o2_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p498 : ((2184401619673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 497, stT301o2 (i+1)) + stT301o2 498 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 497
    simpa using h
  have hprev := st301o2_p497
  have hstep := st301o2_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p499 : ((2344251514231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 498, stT301o2 (i+1)) + stT301o2 499 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 498
    simpa using h
  have hprev := st301o2_p498
  have hstep := st301o2_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_p500 : ((2620710540997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT301o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT301o2 (i+1))
      = (∑ i ∈ Finset.range 499, stT301o2 (i+1)) + stT301o2 500 := by
    have h := Finset.sum_range_succ (fun i => stT301o2 (i+1)) 499
    simpa using h
  have hprev := st301o2_p499
  have hstep := st301o2_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301o2_s500 :
    |Real.sin (((301 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))
      - ((-157199/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log ((500 : ℕ)) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((500 : ℕ)) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact sinMulShift_eval (r := -2260761/10000000) (δ := 3841/500000000) (ψ := 1641/200000) 301 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 301/2`** (evaluated boundary). -/
theorem station_301o2_sign : 0 < hardyG (((((301:ℕ)):ℝ)/2)) := by
  have hcore := phase_station_lower_half_eval 301 500 (by norm_num) (by norm_num)
    ((1641/200000 : ℚ) : ℝ)
  have hchain := st301o2_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT301o2 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((301 : ℕ) : ℝ) * (Real.log ((i+1 : ℕ)) / 2)
              - ((1641/200000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st301o2_c500
  have hsinb := abs_le.mp st301o2_s500
  have hbdy_lo : ((105520427458719/906020000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((301 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ))) / 2
          - ((((301:ℕ)):ℝ)/2)
            * Real.sin (((301 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((1641/200000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((301:ℕ)):ℝ)/2) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((301:ℝ) * (Real.log (500:ℝ) / 2) - ((1641/200000 : ℚ) : ℝ))) / 2
        - ((301:ℝ)/2) * Real.sin ((301:ℝ) * (Real.log (500:ℝ) / 2) - ((1641/200000 : ℚ) : ℝ))
        ≥ ((235951163/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((301:ℝ)/2) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((235951163/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((235951163/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((235951163/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((301:ℕ)):ℝ)/2)+1) * (((((301:ℕ)):ℝ)/2)+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1560661255181/8000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((2620710540997/10000000000000 : ℚ) : ℝ) + ((105520427458719/906020000000000 : ℚ) : ℝ)
      - ((1560661255181/8000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((1641/200000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line (((((301:ℕ)):ℝ)/2)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((1641/200000 : ℚ) : ℝ)
        * (riemannZeta (line (((((301:ℕ)):ℝ)/2)))).re
      - Real.sin ((1641/200000 : ℚ) : ℝ)
        * (riemannZeta (line (((((301:ℕ)):ℝ)/2)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((((301:ℕ)):ℝ)/2))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((((301:ℕ)):ℝ)/2))
      = ((((((301:ℕ)):ℝ)/2)) * (Real.log (((((301:ℕ)):ℝ)/2)) - Real.log 2
          - Real.log Real.pi) - (((((301:ℕ)):ℝ)/2))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM : ((5013963/1000000 : ℚ) : ℝ) ≤ Real.log (((((301:ℕ)):ℝ)/2))
      ∧ Real.log (((((301:ℕ)):ℝ)/2)) ≤ ((3133727/625000 : ℚ) : ℝ) := by
    have hsplit : Real.log (((((301:ℕ)):ℝ)/2))
        = Real.log ((((301:ℕ)):ℝ)) - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    have hM := log_br_301
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
  have hθwin : |(((1641/200000 : ℚ) : ℝ) + ((26:ℤ)) * (2*Real.pi)) - theta (((((301:ℕ)):ℝ)/2))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((((301:ℕ)):ℝ)/2)))
    (φ := ((1641/200000 : ℚ) : ℝ) + ((26:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((1641/200000 : ℚ)) : ℝ) 26).1,
    (cos_sin_shift (((1641/200000 : ℚ)) : ℝ) 26).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_301o2_sign
end AxiomAudit
