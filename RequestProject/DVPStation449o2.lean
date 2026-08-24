import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationHalfEval

/-!
# Station `t = 449/2` (rung-235.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT449o2 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((449 : ℕ) : ℝ) * (Real.log ((n : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))

theorem st449o2_c1 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((968881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((0 : ℚ) : ℝ) ≤ Real.log ((1 : ℕ)) / 2 := by
    have h := (log_br_1).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((1 : ℕ)) / 2 ≤ ((0 : ℚ) : ℝ) := by
    have h := (log_br_1).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 125063/2000000) (δ := 1/1000000000) (ψ := -125063/500000) 449 0
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t1 : ((968831/1000000 : ℚ) : ℝ) ≤ stT449o2 1 := by
  have hc : ((968831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((968831/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((968831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c2 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((6911/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log ((2 : ℕ)) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((2 : ℕ)) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3044929/10000000) (δ := 5661/500000000) (ψ := -125063/500000) 449 25
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t2 : ((4886107297/20000000000 : ℚ) : ℝ) ≤ stT449o2 2 := by
  have hc : ((691/2000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4886107297/20000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((691/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c3 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-135077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log ((3 : ℕ)) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((3 : ℕ)) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4610873/10000000) (δ := 5641/500000000) (ψ := -125063/500000) 449 39
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t3 : ((-390005901153/2500000000000 : ℚ) : ℝ) ≤ stT449o2 3 := by
  have hc : ((-67551/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-390005901153/2500000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-67551/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c4 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-449013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log ((4 : ℕ)) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((4 : ℕ)) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -839393/1250000) (δ := 1141/100000000) (ψ := -125063/500000) 449 50
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t4 : ((-1122595224519/2500000000000 : ℚ) : ℝ) ≤ stT449o2 4 := by
  have hc : ((-224519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1122595224519/2500000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-224519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c5 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-959439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log ((5 : ℕ)) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((5 : ℕ)) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1427901/2000000) (δ := 2817/250000000) (ψ := -125063/500000) 449 58
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t5 : ((-536370662313/1250000000000 : ℚ) : ℝ) ≤ stT449o2 5 := by
  have hc : ((-959489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-536370662313/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-959489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c6 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((232511/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log ((6 : ℕ)) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((6 : ℕ)) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 940657/10000000) (δ := 2823/250000000) (ψ := -125063/500000) 449 64
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t6 : ((949170941277/2500000000000 : ℚ) : ℝ) ≤ stT449o2 6 := by
  have hc : ((464997/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((949170941277/2500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((464997/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c7 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-910801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log ((7 : ℕ)) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((7 : ℕ)) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3395021/5000000) (δ := 5627/500000000) (ψ := -125063/500000) 449 70
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t7 : ((-688538685579/2000000000000 : ℚ) : ℝ) ≤ stT449o2 7 := by
  have hc : ((-910851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-688538685579/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-910851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c8 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-264849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log ((8 : ℕ)) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((8 : ℕ)) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5322603/10000000) (δ := 1127/100000000) (ψ := -125063/500000) 449 74
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t8 : ((-234117758179/1250000000000 : ℚ) : ℝ) ≤ stT449o2 8 := by
  have hc : ((-132437/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234117758179/1250000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-132437/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c9 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-956221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log ((9 : ℕ)) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((9 : ℕ)) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -444469/625000) (δ := 11419/1000000000) (ψ := -125063/500000) 449 79
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t9 : ((-1593785318757/5000000000000 : ℚ) : ℝ) ≤ stT449o2 9 := by
  have hc : ((-956271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1593785318757/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-956271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c10 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-18939/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log ((10 : ℕ)) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((10 : ℕ)) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2449093/5000000) (δ := 11363/1000000000) (ψ := -125063/500000) 449 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t10 : ((-59898288737/500000000000 : ℚ) : ℝ) ≤ stT449o2 10 := by
  have hc : ((-37883/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59898288737/500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-37883/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c11 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-102043/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log ((11 : ℕ)) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((11 : ℕ)) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4440817/10000000) (δ := 5617/500000000) (ψ := -125063/500000) 449 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t11 : ((-38468331969/625000000000 : ℚ) : ℝ) ≤ stT449o2 11 := by
  have hc : ((-25517/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38468331969/625000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-25517/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c12 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((115217/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log ((12 : ℕ)) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((12 : ℕ)) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2729559/10000000) (δ := 11413/1000000000) (ψ := -125063/500000) 449 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t12 : ((665133411159/5000000000000 : ℚ) : ℝ) ≤ stT449o2 12 := by
  have hc : ((230409/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((665133411159/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((230409/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c13 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-6099/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log ((13 : ℕ)) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((13 : ℕ)) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4929483/10000000) (δ := 11241/1000000000) (ψ := -125063/500000) 449 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t13 : ((-541367980693/5000000000000 : ℚ) : ℝ) ≤ stT449o2 13 := by
  have hc : ((-195193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-541367980693/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-195193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c14 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-252027/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log ((14 : ℕ)) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((14 : ℕ)) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2623853/5000000) (δ := 5713/500000000) (ψ := -125063/500000) 449 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t14 : ((-168409362969/1250000000000 : ℚ) : ℝ) ≤ stT449o2 14 := by
  have hc : ((-63013/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168409362969/1250000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-63013/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c15 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((76081/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log ((15 : ℕ)) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((15 : ℕ)) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3153919/10000000) (δ := 5649/500000000) (ψ := -125063/500000) 449 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t15 : ((98203977089/1250000000000 : ℚ) : ℝ) ≤ stT449o2 15 := by
  have hc : ((152137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98203977089/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((152137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c16 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((394703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log ((16 : ℕ)) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((16 : ℕ)) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1652387/10000000) (δ := 11391/1000000000) (ψ := -125063/500000) 449 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t16 : ((197339/1000000 : ℚ) : ℝ) ≤ stT449o2 16 := by
  have hc : ((197339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197339/1000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((197339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c17 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-13361/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log ((17 : ℕ)) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((17 : ℕ)) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2131009/5000000) (δ := 11377/1000000000) (ψ := -125063/500000) 449 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t17 : ((-16208660831/500000000000 : ℚ) : ℝ) ≤ stT449o2 17 := by
  have hc : ((-6683/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16208660831/500000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-6683/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c18 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-389143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log ((18 : ℕ)) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((18 : ℕ)) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4926243/10000000) (δ := 5631/500000000) (ψ := -125063/500000) 449 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t18 : ((-917336852439/10000000000000 : ℚ) : ℝ) ≤ stT449o2 18 := by
  have hc : ((-389193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-917336852439/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-389193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c19 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((28579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log ((19 : ℕ)) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((19 : ℕ)) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3855533/10000000) (δ := 2281/200000000) (ψ := -125063/500000) 449 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t19 : ((65450005053/10000000000000 : ℚ) : ℝ) ≤ stT449o2 19 := by
  have hc : ((28529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65450005053/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((28529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c20 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((881773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log ((20 : ℕ)) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((20 : ℕ)) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1227971/10000000) (δ := 1137/100000000) (ψ := -125063/500000) 449 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t20 : ((1971591703441/10000000000000 : ℚ) : ℝ) ≤ stT449o2 20 := by
  have hc : ((881723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1971591703441/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((881723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c21 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((434077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log ((21 : ℕ)) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((21 : ℕ)) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -350557/1250000) (δ := 2821/250000000) (ψ := -125063/500000) 449 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t21 : ((473562085403/5000000000000 : ℚ) : ℝ) ≤ stT449o2 21 := by
  have hc : ((434027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((473562085403/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((434027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c22 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-994719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log ((22 : ℕ)) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((22 : ℕ)) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7596931/10000000) (δ := 11391/1000000000) (ψ := -125063/500000) 449 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t22 : ((-265106933269/1250000000000 : ℚ) : ℝ) ≤ stT449o2 22 := by
  have hc : ((-994769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265106933269/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-994769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c23 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((899649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log ((23 : ℕ)) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((23 : ℕ)) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1129577/10000000) (δ := 5653/500000000) (ψ := -125063/500000) 449 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t23 : ((234474182157/1250000000000 : ℚ) : ℝ) ≤ stT449o2 23 := by
  have hc : ((899599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234474182157/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((899599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c24 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-835539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log ((24 : ℕ)) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((24 : ℕ)) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3199887/5000000) (δ := 283/25000000) (ψ := -125063/500000) 449 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t24 : ((-852819680769/5000000000000 : ℚ) : ℝ) ≤ stT449o2 24 := by
  have hc : ((-835589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-852819680769/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-835589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c25 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((47439/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log ((25 : ℕ)) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((25 : ℕ)) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 80361/1000000) (δ := 11227/1000000000) (ψ := -125063/500000) 449 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t25 : ((94873/500000 : ℚ) : ℝ) ≤ stT449o2 25 := by
  have hc : ((94873/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94873/500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((94873/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c26 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-955841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log ((26 : ℕ)) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((26 : ℕ)) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1421653/2000000) (δ := 1423/125000000) (ψ := -125063/500000) 449 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t26 : ((-937328552671/5000000000000 : ℚ) : ℝ) ≤ stT449o2 26 := by
  have hc : ((-955891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-937328552671/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-955891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c27 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((314973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log ((27 : ℕ)) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((27 : ℕ)) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3125919/10000000) (δ := 2851/250000000) (ψ := -125063/500000) 449 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t27 : ((1212138627/20000000000 : ℚ) : ℝ) ≤ stT449o2 27 := by
  have hc : ((314923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1212138627/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((314923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c28 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((10093/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log ((28 : ℕ)) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((28 : ℕ)) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 157749/1000000) (δ := 5653/500000000) (ψ := -125063/500000) 449 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t28 : ((76291169229/500000000000 : ℚ) : ℝ) ≤ stT449o2 28 := by
  have hc : ((80739/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76291169229/500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((80739/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c29 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-38073/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log ((29 : ℕ)) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((29 : ℕ)) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5564519/10000000) (δ := 11363/1000000000) (ψ := -125063/500000) 449 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t29 : ((-282822450493/2500000000000 : ℚ) : ℝ) ≤ stT449o2 29 := by
  have hc : ((-304609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282822450493/2500000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-304609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c30 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-183271/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log ((30 : ℕ)) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((30 : ℕ)) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6824191/10000000) (δ := 11227/1000000000) (ψ := -125063/500000) 449 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t30 : ((-167311909751/1000000000000 : ℚ) : ℝ) ≤ stT449o2 30 := by
  have hc : ((-183281/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167311909751/1000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-183281/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c31 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-16129/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log ((31 : ℕ)) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((31 : ℕ)) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4128823/10000000) (δ := 2817/250000000) (ψ := -125063/500000) 449 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t31 : ((-14493257753/1000000000000 : ℚ) : ℝ) ≤ stT449o2 31 := by
  have hc : ((-16139/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14493257753/1000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-16139/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c32 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((691573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log ((32 : ℕ)) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((32 : ℕ)) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -504457/2500000) (δ := 5671/500000000) (ψ := -125063/500000) 449 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t32 : ((611225423809/5000000000000 : ℚ) : ℝ) ≤ stT449o2 32 := by
  have hc : ((691523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((611225423809/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((691523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c33 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((983467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log ((33 : ℕ)) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((33 : ℕ)) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -455231/10000000) (δ := 11249/1000000000) (ψ := -125063/500000) 449 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t33 : ((213988588949/1250000000000 : ℚ) : ℝ) ≤ stT449o2 33 := by
  have hc : ((983417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213988588949/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((983417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c34 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((60757/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log ((34 : ℕ)) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((34 : ℕ)) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 295901/5000000) (δ := 1407/125000000) (ψ := -125063/500000) 449 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t34 : ((166707174907/1000000000000 : ℚ) : ℝ) ≤ stT449o2 34 := by
  have hc : ((486031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166707174907/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((486031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c35 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((447753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log ((35 : ℕ)) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((35 : ℕ)) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1153073/10000000) (δ := 281/25000000) (ψ := -125063/500000) 449 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t35 : ((11824972191/78125000000 : ℚ) : ℝ) ≤ stT449o2 35 := by
  have hc : ((27983/31250 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11824972191/78125000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((27983/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c36 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((109553/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log ((36 : ℕ)) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((36 : ℕ)) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1256027/10000000) (δ := 11383/1000000000) (ψ := -125063/500000) 449 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t36 : ((365155687271/2500000000000 : ℚ) : ℝ) ≤ stT449o2 36 := by
  have hc : ((438187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365155687271/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((438187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c37 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((466109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log ((37 : ℕ)) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((37 : ℕ)) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 925753/10000000) (δ := 5639/500000000) (ψ := -125063/500000) 449 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t37 : ((191559242269/1250000000000 : ℚ) : ℝ) ≤ stT449o2 37 := by
  have hc : ((116521/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191559242269/1250000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((116521/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c38 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((498627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log ((38 : ℕ)) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((38 : ℕ)) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 185317/10000000) (δ := 2257/200000000) (ψ := -125063/500000) 449 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t38 : ((202209786207/1250000000000 : ℚ) : ℝ) ≤ stT449o2 38 := by
  have hc : ((249301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202209786207/1250000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((249301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c39 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((929567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log ((39 : ℕ)) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((39 : ℕ)) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -943897/10000000) (δ := 5621/500000000) (ψ := -125063/500000) 449 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t39 : ((1488417911277/10000000000000 : ℚ) : ℝ) ≤ stT449o2 39 := by
  have hc : ((929517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1488417911277/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((929517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c40 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((139899/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log ((40 : ℕ)) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((40 : ℕ)) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -488449/2000000) (δ := 11249/1000000000) (ψ := -125063/500000) 449 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t40 : ((221179860837/2500000000000 : ℚ) : ℝ) ≤ stT449o2 40 := by
  have hc : ((279773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221179860837/2500000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((279773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c41 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-72641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log ((41 : ℕ)) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((41 : ℕ)) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4291487/10000000) (δ := 11397/1000000000) (ψ := -125063/500000) 449 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t41 : ((-28371313377/1250000000000 : ℚ) : ℝ) ≤ stT449o2 41 := by
  have hc : ((-36333/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28371313377/1250000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-36333/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c42 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-425811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log ((42 : ℕ)) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((42 : ℕ)) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -404667/625000) (δ := 11289/1000000000) (ψ := -125063/500000) 449 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t42 : ((-82134928303/625000000000 : ℚ) : ℝ) ≤ stT449o2 42 := by
  have hc : ((-106459/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82134928303/625000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-106459/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c43 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-900941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log ((43 : ℕ)) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((43 : ℕ)) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6731821/10000000) (δ := 11339/1000000000) (ψ := -125063/500000) 449 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t43 : ((-686999330563/5000000000000 : ℚ) : ℝ) ≤ stT449o2 43 := by
  have hc : ((-900991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-686999330563/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-900991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c44 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((11/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log ((44 : ℕ)) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((44 : ℕ)) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 785343/2000000) (δ := 11271/1000000000) (ψ := -125063/500000) 449 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t44 : ((1130667/125000000000 : ℚ) : ℝ) ≤ stT449o2 44 := by
  have hc : ((3/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1130667/125000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((3/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c45 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((472591/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log ((45 : ℕ)) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((45 : ℕ)) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 831611/10000000) (δ := 5689/500000000) (ψ := -125063/500000) 449 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t45 : ((352229667213/2500000000000 : ℚ) : ℝ) ≤ stT449o2 45 := by
  have hc : ((236283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352229667213/2500000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((236283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c46 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((263267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log ((46 : ℕ)) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((46 : ℕ)) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -508139/2000000) (δ := 2247/200000000) (ψ := -125063/500000) 449 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t46 : ((194064503199/2500000000000 : ℚ) : ℝ) ≤ stT449o2 46 := by
  have hc : ((131621/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194064503199/2500000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((131621/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c47 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-783639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log ((47 : ℕ)) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((47 : ℕ)) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6178247/10000000) (δ := 89/7812500) (ψ := -125063/500000) 449 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t47 : ((-22862559197/200000000000 : ℚ) : ℝ) ≤ stT449o2 47 := by
  have hc : ((-783689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22862559197/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-783689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c48 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-632203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log ((48 : ℕ)) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((48 : ℕ)) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5637973/10000000) (δ := 11361/1000000000) (ψ := -125063/500000) 449 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t48 : ((-57036175383/625000000000 : ℚ) : ℝ) ≤ stT449o2 48 := by
  have hc : ((-632253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57036175383/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-632253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c49 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((412381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log ((49 : ℕ)) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((49 : ℕ)) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 187817/1250000) (δ := 5627/500000000) (ψ := -125063/500000) 449 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t49 : ((147269955819/1250000000000 : ℚ) : ℝ) ≤ stT449o2 49 := by
  have hc : ((103089/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147269955819/1250000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((103089/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c50 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((8231/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log ((50 : ℕ)) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((50 : ℕ)) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1433303/5000000) (δ := 5673/500000000) (ψ := -125063/500000) 449 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t50 : ((1163897299/20000000000 : ℚ) : ℝ) ≤ stT449o2 50 := by
  have hc : ((823/2000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1163897299/20000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((823/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c51 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-987631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log ((51 : ℕ)) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((51 : ℕ)) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -186509/250000) (δ := 11339/1000000000) (ψ := -125063/500000) 449 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t51 : ((-1383030938361/10000000000000 : ℚ) : ℝ) ≤ stT449o2 51 := by
  have hc : ((-987681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1383030938361/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-987681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c52 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((48583/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log ((52 : ℕ)) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((52 : ℕ)) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3438049/10000000) (δ := 22/1953125) (ψ := -125063/500000) 449 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t52 : ((538841127/20000000000 : ℚ) : ℝ) ≤ stT449o2 52 := by
  have hc : ((97141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((538841127/20000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((97141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c53 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((807057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log ((53 : ℕ)) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((53 : ℕ)) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -197389/1250000) (δ := 11271/1000000000) (ψ := -125063/500000) 449 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t53 : ((221701770047/2000000000000 : ℚ) : ℝ) ≤ stT449o2 53 := by
  have hc : ((807007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221701770047/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((807007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c54 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-227951/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log ((54 : ℕ)) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((54 : ℕ)) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3398067/5000000) (δ := 177/15625000) (ψ := -125063/500000) 449 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t54 : ((-155109556889/1250000000000 : ℚ) : ℝ) ≤ stT449o2 54 := by
  have hc : ((-455927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155109556889/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-455927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c55 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((169061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log ((55 : ℕ)) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((55 : ℕ)) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1751149/5000000) (δ := 451/40000000) (ψ := -125063/500000) 449 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t55 : ((227894263389/10000000000000 : ℚ) : ℝ) ≤ stT449o2 55 := by
  have hc : ((169011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227894263389/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((169011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c56 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((66961/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log ((56 : ℕ)) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((56 : ℕ)) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1046391/5000000) (δ := 2247/200000000) (ψ := -125063/500000) 449 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t56 : ((11184213067/125000000000 : ℚ) : ℝ) ≤ stT449o2 56 := by
  have hc : ((16739/25000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11184213067/125000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((16739/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c57 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-999987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log ((57 : ℕ)) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((57 : ℕ)) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3920559/5000000) (δ := 5709/500000000) (ψ := -125063/500000) 449 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t57 : ((-1324582007721/10000000000000 : ℚ) : ℝ) ≤ stT449o2 57 := by
  have hc : ((-1000037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1324582007721/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-1000037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c58 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((181601/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log ((58 : ℕ)) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((58 : ℕ)) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1894303/10000000) (δ := 11243/1000000000) (ψ := -125063/500000) 449 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t58 : ((59609330541/625000000000 : ℚ) : ℝ) ≤ stT449o2 58 := by
  have hc : ((363177/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59609330541/625000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((363177/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c59 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-29177/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log ((59 : ℕ)) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((59 : ℕ)) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1054857/2500000) (δ := 227/20000000) (ψ := -125063/500000) 449 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t59 : ((-7600303631/500000000000 : ℚ) : ℝ) ≤ stT449o2 59 := by
  have hc : ((-58379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7600303631/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-58379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c60 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-49221/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log ((60 : ℕ)) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((60 : ℕ)) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5213557/10000000) (δ := 57/5000000) (ψ := -125063/500000) 449 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t60 : ((-6355051987/100000000000 : ℚ) : ℝ) ≤ stT449o2 60 := by
  have hc : ((-24613/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6355051987/100000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-24613/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c61 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((883771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log ((61 : ℕ)) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((61 : ℕ)) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1217337/10000000) (δ := 11257/1000000000) (ψ := -125063/500000) 449 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t61 : ((70718005583/625000000000 : ℚ) : ℝ) ≤ stT449o2 61 := by
  have hc : ((883721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70718005583/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((883721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c62 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-999759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log ((62 : ℕ)) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((62 : ℕ)) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1559819/2000000) (δ := 11339/1000000000) (ψ := -125063/500000) 449 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t62 : ((-634879714809/5000000000000 : ℚ) : ℝ) ≤ stT449o2 62 := by
  have hc : ((-999809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-634879714809/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-999809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c63 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((178091/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log ((63 : ℕ)) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((63 : ℕ)) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 118113/1000000) (δ := 5657/500000000) (ψ := -125063/500000) 449 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t63 : ((224360868361/2000000000000 : ℚ) : ℝ) ≤ stT449o2 63 := by
  have hc : ((178081/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224360868361/2000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((178081/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c64 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-64761/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log ((64 : ℕ)) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((64 : ℕ)) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -56881/100000) (δ := 11271/1000000000) (ψ := -125063/500000) 449 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t64 : ((-40478782383/500000000000 : ℚ) : ℝ) ≤ stT449o2 64 := by
  have hc : ((-32383/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40478782383/500000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-32383/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c65 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((35727/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log ((65 : ℕ)) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((65 : ℕ)) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 23544/78125) (δ := 5641/500000000) (ψ := -125063/500000) 449 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t65 : ((22153837767/500000000000 : ℚ) : ℝ) ≤ stT449o2 65 := by
  have hc : ((17861/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22153837767/500000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((17861/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c66 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-79299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log ((66 : ℕ)) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((66 : ℕ)) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4125447/10000000) (δ := 453/40000000) (ψ := -125063/500000) 449 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t66 : ((-19534374867/2000000000000 : ℚ) : ℝ) ≤ stT449o2 66 := by
  have hc : ((-79349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19534374867/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-79349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c67 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-154413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log ((67 : ℕ)) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((67 : ℕ)) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 172583/400000) (δ := 5689/500000000) (ψ := -125063/500000) 449 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t67 : ((-37741334957/2000000000000 : ℚ) : ℝ) ≤ stT449o2 67 := by
  have hc : ((-154463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37741334957/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-154463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c68 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((6659/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log ((68 : ℕ)) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((68 : ℕ)) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1539207/5000000) (δ := 11317/1000000000) (ψ := -125063/500000) 449 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t68 : ((2018502531/50000000000 : ℚ) : ℝ) ≤ stT449o2 68 := by
  have hc : ((3329/10000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2018502531/50000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((3329/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c69 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-228789/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log ((69 : ℕ)) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((69 : ℕ)) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5115163/10000000) (δ := 1417/125000000) (ψ := -125063/500000) 449 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t69 : ((-137729896613/2500000000000 : ℚ) : ℝ) ≤ stT449o2 69 := by
  have hc : ((-114407/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137729896613/2500000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-114407/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c70 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((13363/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log ((70 : ℕ)) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((70 : ℕ)) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2517143/10000000) (δ := 71/6250000) (ψ := -125063/500000) 449 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t70 : ((15970337729/250000000000 : ℚ) : ℝ) ≤ stT449o2 70 := by
  have hc : ((53447/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15970337729/250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((53447/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c71 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-570233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log ((71 : ℕ)) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((71 : ℕ)) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1360991/2500000) (δ := 563/50000000) (ψ := -125063/500000) 449 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t71 : ((-338400799653/5000000000000 : ℚ) : ℝ) ≤ stT449o2 71 := by
  have hc : ((-570283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-338400799653/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-570283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c72 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((284431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log ((72 : ℕ)) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((72 : ℕ)) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -603547/2500000) (δ := 227/20000000) (ψ := -125063/500000) 449 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t72 : ((167587799733/2500000000000 : ℚ) : ℝ) ≤ stT449o2 72 := by
  have hc : ((142203/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167587799733/2500000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((142203/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c73 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-531291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log ((73 : ℕ)) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((73 : ℕ)) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5327301/10000000) (δ := 11353/1000000000) (ψ := -125063/500000) 449 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t73 : ((-155471970623/2500000000000 : ℚ) : ℝ) ≤ stT449o2 73 := by
  have hc : ((-531341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155471970623/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-531341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c74 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((455549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log ((74 : ℕ)) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((74 : ℕ)) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2744519/10000000) (δ := 5623/500000000) (ψ := -125063/500000) 449 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t74 : ((132376663881/2500000000000 : ℚ) : ℝ) ≤ stT449o2 74 := by
  have hc : ((455499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132376663881/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((455499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c75 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-169043/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log ((75 : ℕ)) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((75 : ℕ)) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1197299/2500000) (δ := 11257/1000000000) (ψ := -125063/500000) 449 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t75 : ((-48805747167/1250000000000 : ℚ) : ℝ) ≤ stT449o2 75 := by
  have hc : ((-42267/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48805747167/1250000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-42267/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c76 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((175917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log ((76 : ℕ)) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((76 : ℕ)) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3484899/10000000) (δ := 11289/1000000000) (ψ := -125063/500000) 449 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t76 : ((100866583313/5000000000000 : ℚ) : ℝ) ≤ stT449o2 76 := by
  have hc : ((175867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100866583313/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((175867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c77 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((6013/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log ((77 : ℕ)) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((77 : ℕ)) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3851817/10000000) (δ := 11339/1000000000) (ψ := -125063/500000) 449 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t77 : ((1368209763/400000000000 : ℚ) : ℝ) ≤ stT449o2 77 := by
  have hc : ((6003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1368209763/400000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((6003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c78 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-271401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log ((78 : ℕ)) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((78 : ℕ)) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4614113/10000000) (δ := 11331/1000000000) (ψ := -125063/500000) 449 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t78 : ((-153678997689/5000000000000 : ℚ) : ℝ) ≤ stT449o2 78 := by
  have hc : ((-271451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153678997689/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-271451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c79 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((66031/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log ((79 : ℕ)) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((79 : ℕ)) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2535651/10000000) (δ := 11231/1000000000) (ψ := -125063/500000) 449 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t79 : ((297134351613/5000000000000 : ℚ) : ℝ) ≤ stT449o2 79 := by
  have hc : ((264099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((297134351613/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((264099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c80 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-767023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log ((80 : ℕ)) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((80 : ℕ)) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6112461/10000000) (δ := 2831/250000000) (ψ := -125063/500000) 449 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t80 : ((-428806847241/5000000000000 : ℚ) : ℝ) ≤ stT449o2 80 := by
  have hc : ((-767073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-428806847241/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-767073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c81 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((470729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log ((81 : ℕ)) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((81 : ℕ)) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 859667/10000000) (δ := 5687/500000000) (ψ := -125063/500000) 449 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t81 : ((32687774509/312500000000 : ℚ) : ℝ) ≤ stT449o2 81 := by
  have hc : ((29419/31250 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32687774509/312500000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((29419/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c82 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-31221/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log ((82 : ℕ)) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((82 : ℕ)) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7746261/10000000) (δ := 11229/1000000000) (ψ := -125063/500000) 449 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t82 : ((-137918301319/1250000000000 : ℚ) : ℝ) ≤ stT449o2 82 := by
  have hc : ((-499561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137918301319/1250000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-499561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c83 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((447263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log ((83 : ℕ)) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((83 : ℕ)) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1158567/10000000) (δ := 11417/1000000000) (ψ := -125063/500000) 449 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t83 : ((122726803199/1250000000000 : ℚ) : ℝ) ≤ stT449o2 83 := by
  have hc : ((223619/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122726803199/1250000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((223619/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c84 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-608701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log ((84 : ℕ)) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((84 : ℕ)) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 695381/1250000) (δ := 11293/500000000) (ψ := -125063/500000) 449 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t84 : ((-66420212859/1000000000000 : ℚ) : ℝ) ≤ stT449o2 84 := by
  have hc : ((-608751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66420212859/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-608751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c85 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((168851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log ((85 : ℕ)) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((85 : ℕ)) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3502831/10000000) (δ := 1141/100000000) (ψ := -125063/500000) 449 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t85 : ((45772585563/2500000000000 : ℚ) : ℝ) ≤ stT449o2 85 := by
  have hc : ((168801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45772585563/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((168801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c86 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((42413/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log ((86 : ℕ)) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((86 : ℕ)) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3061549/10000000) (δ := 1141/100000000) (ψ := -125063/500000) 449 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t86 : ((182913374029/5000000000000 : ℚ) : ℝ) ≤ stT449o2 86 := by
  have hc : ((169627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182913374029/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((169627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c87 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-778547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log ((87 : ℕ)) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((87 : ℕ)) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6157859/10000000) (δ := 11353/1000000000) (ψ := -125063/500000) 449 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t87 : ((-834743965461/10000000000000 : ℚ) : ℝ) ≤ stT449o2 87 := by
  have hc : ((-778597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-834743965461/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-778597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c88 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((994741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log ((88 : ℕ)) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((88 : ℕ)) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 256499/10000000) (δ := 11303/1000000000) (ψ := -125063/500000) 449 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t88 : ((1060343590073/10000000000000 : ℚ) : ℝ) ≤ stT449o2 88 := by
  have hc : ((994691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1060343590073/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((994691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c89 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-876499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log ((89 : ℕ)) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((89 : ℕ)) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 824793/1250000) (δ := 57/5000000) (ψ := -125063/500000) 449 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t89 : ((-464570093451/5000000000000 : ℚ) : ℝ) ≤ stT449o2 89 := by
  have hc : ((-876549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-464570093451/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-876549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c90 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((105433/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log ((90 : ℕ)) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((90 : ℕ)) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -567721/2000000) (δ := 11257/1000000000) (ψ := -125063/500000) 449 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t90 : ((55561452843/1250000000000 : ℚ) : ℝ) ≤ stT449o2 90 := by
  have hc : ((210841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55561452843/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((210841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c91 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((5591/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log ((91 : ℕ)) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((91 : ℕ)) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3363123/10000000) (δ := 11273/500000000) (ψ := -125063/500000) 449 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t91 : ((5859645489/250000000000 : ℚ) : ℝ) ≤ stT449o2 91 := by
  have hc : ((22359/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5859645489/250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((22359/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c92 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-791689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log ((92 : ℕ)) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((92 : ℕ)) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6210911/10000000) (δ := 5669/500000000) (ψ := -125063/500000) 449 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t92 : ((-825445704447/10000000000000 : ℚ) : ℝ) ≤ stT449o2 92 := by
  have hc : ((-791739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-825445704447/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-791739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c93 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((499179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log ((93 : ℕ)) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((93 : ℕ)) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -143293/10000000) (δ := 2253/200000000) (ψ := -125063/500000) 449 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t93 : ((258799119727/2500000000000 : ℚ) : ℝ) ≤ stT449o2 93 := by
  have hc : ((249577/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258799119727/2500000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((249577/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c94 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-21821/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log ((94 : ℕ)) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((94 : ℕ)) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1464861/2500000) (δ := 5619/500000000) (ψ := -125063/500000) 449 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t94 : ((-180066168471/2500000000000 : ℚ) : ℝ) ≤ stT449o2 94 := by
  have hc : ((-349161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180066168471/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-349161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c95 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((707/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log ((95 : ℕ)) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((95 : ℕ)) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -977329/2500000) (δ := 11381/1000000000) (ψ := -125063/500000) 449 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t95 : ((180059139/250000000000 : ℚ) : ℝ) ≤ stT449o2 95 := by
  have hc : ((351/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180059139/250000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((351/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c96 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((176479/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log ((96 : ℕ)) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((96 : ℕ)) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 983851/5000000) (δ := 5711/500000000) (ψ := -125063/500000) 449 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t96 : ((18010523923/250000000000 : ℚ) : ℝ) ≤ stT449o2 96 := by
  have hc : ((352933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18010523923/250000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((352933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c97 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-499803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log ((97 : ℕ)) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((97 : ℕ)) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7783823/10000000) (δ := 11231/1000000000) (ψ := -125063/500000) 449 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t97 : ((-126874715079/1250000000000 : ℚ) : ℝ) ≤ stT449o2 97 := by
  have hc : ((-124957/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126874715079/1250000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-124957/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c98 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((323531/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log ((98 : ℕ)) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((98 : ℕ)) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3387/15625) (δ := 5687/500000000) (ψ := -125063/500000) 449 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t98 : ((20424389557/312500000000 : ℚ) : ℝ) ≤ stT449o2 98 := by
  have hc : ((161753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20424389557/312500000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((161753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c99 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((15799/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log ((99 : ℕ)) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((99 : ℕ)) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 706071/2000000) (δ := 11279/1000000000) (ψ := -125063/500000) 449 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t99 : ((7936777189/500000000000 : ℚ) : ℝ) ≤ stT449o2 99 := by
  have hc : ((7897/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7936777189/500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((7897/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c100 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-2161/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log ((100 : ℕ)) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((100 : ℕ)) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3268439/5000000) (δ := 11417/1000000000) (ψ := -125063/500000) 449 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t100 : ((-17289/200000 : ℚ) : ℝ) ≤ stT449o2 100 := by
  have hc : ((-17289/20000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17289/200000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-17289/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c101 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((185667/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log ((101 : ℕ)) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((101 : ℕ)) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -119027/1250000) (δ := 11417/1000000000) (ψ := -125063/500000) 449 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t101 : ((184735584309/2000000000000 : ℚ) : ℝ) ≤ stT449o2 101 := by
  have hc : ((185657/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184735584309/2000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((185657/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c102 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-128617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log ((102 : ℕ)) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((102 : ℕ)) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1144347/2500000) (δ := 5643/500000000) (ψ := -125063/500000) 449 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t102 : ((-15921827377/625000000000 : ℚ) : ℝ) ≤ stT449o2 102 := by
  have hc : ((-64321/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15921827377/625000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-64321/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c103 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-318727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log ((103 : ℕ)) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((103 : ℕ)) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1413741/2500000) (δ := 11343/1000000000) (ψ := -125063/500000) 449 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t103 : ((-981487213/15625000000 : ℚ) : ℝ) ≤ stT449o2 103 := by
  have hc : ((-9961/15625 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-981487213/15625000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-9961/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c104 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((995689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log ((104 : ℕ)) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((104 : ℕ)) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -232223/10000000) (δ := 563/50000000) (ψ := -125063/500000) 449 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t104 : ((48815184531/500000000000 : ℚ) : ℝ) ≤ stT449o2 104 := by
  have hc : ((995639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48815184531/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((995639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c105 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-232957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log ((105 : ℕ)) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((105 : ℕ)) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5138659/10000000) (δ := 11243/1000000000) (ψ := -125063/500000) 449 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t105 : ((-113683683391/2500000000000 : ℚ) : ℝ) ≤ stT449o2 105 := by
  have hc : ((-116491/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113683683391/2500000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-116491/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c106 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-504633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log ((106 : ℕ)) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((106 : ℕ)) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -656173/1250000) (δ := 11253/1000000000) (ψ := -125063/500000) 449 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t106 : ((-245095766169/5000000000000 : ℚ) : ℝ) ≤ stT449o2 106 := by
  have hc : ((-504683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245095766169/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-504683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c107 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((499983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log ((107 : ℕ)) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((107 : ℕ)) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 20641/10000000) (δ := 11353/1000000000) (ψ := -125063/500000) 449 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t107 : ((15103981159/156250000000 : ℚ) : ℝ) ≤ stT449o2 107 := by
  have hc : ((249979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15103981159/156250000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((249979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c108 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-501947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log ((108 : ℕ)) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((108 : ℕ)) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5241613/10000000) (δ := 11353/1000000000) (ψ := -125063/500000) 449 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t108 : ((-483047115247/10000000000000 : ℚ) : ℝ) ≤ stT449o2 108 := by
  have hc : ((-501997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483047115247/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-501997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c109 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-2599/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log ((109 : ℕ)) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((109 : ℕ)) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5293533/10000000) (δ := 2827/250000000) (ψ := -125063/500000) 449 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t109 : ((-9958527319/200000000000 : ℚ) : ℝ) ≤ stT449o2 109 := by
  have hc : ((-10397/20000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9958527319/200000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-10397/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c110 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((199549/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log ((110 : ℕ)) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((110 : ℕ)) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -83959/5000000) (δ := 2279/200000000) (ψ := -125063/500000) 449 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t110 : ((95126427009/1000000000000 : ℚ) : ℝ) ≤ stT449o2 110 := by
  have hc : ((199539/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95126427009/1000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((199539/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c111 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-95911/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log ((111 : ℕ)) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((111 : ℕ)) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4911339/10000000) (δ := 2827/250000000) (ψ := -125063/500000) 449 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t111 : ((-91046557413/2500000000000 : ℚ) : ℝ) ≤ stT449o2 111 := by
  have hc : ((-191847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91046557413/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-191847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c112 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-10471/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log ((112 : ℕ)) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((112 : ℕ)) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2881499/5000000) (δ := 5669/500000000) (ψ := -125063/500000) 449 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t112 : ((-19789823529/312500000000 : ℚ) : ℝ) ≤ stT449o2 112 := by
  have hc : ((-335097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19789823529/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-335097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c113 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((19049/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log ((113 : ℕ)) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((113 : ℕ)) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -387023/5000000) (δ := 2283/200000000) (ψ := -125063/500000) 449 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t113 : ((27998179/312500000 : ℚ) : ℝ) ≤ stT449o2 113 := by
  have hc : ((2381/2500 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27998179/312500000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((2381/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c114 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-9741/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log ((114 : ℕ)) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((114 : ℕ)) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4170903/10000000) (δ := 2263/200000000) (ψ := -125063/500000) 449 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t114 : ((-2281991789/250000000000 : ℚ) : ℝ) ≤ stT449o2 114 := by
  have hc : ((-4873/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2281991789/250000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-4873/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c115 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-441757/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log ((115 : ℕ)) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((115 : ℕ)) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6635271/10000000) (δ := 2843/250000000) (ψ := -125063/500000) 449 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t115 : ((-41196392391/500000000000 : ℚ) : ℝ) ≤ stT449o2 115 := by
  have hc : ((-220891/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41196392391/500000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-220891/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c116 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((758109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log ((116 : ℕ)) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((116 : ℕ)) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1775969/10000000) (δ := 11281/1000000000) (ψ := -125063/500000) 449 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t116 : ((175959897021/2500000000000 : ℚ) : ℝ) ≤ stT449o2 116 := by
  have hc : ((758059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175959897021/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((758059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c117 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((173383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log ((117 : ℕ)) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((117 : ℕ)) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3041689/10000000) (δ := 1409/125000000) (ψ := -125063/500000) 449 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t117 : ((160269471/5000000000 : ℚ) : ℝ) ≤ stT449o2 117 := by
  have hc : ((86679/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160269471/5000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((86679/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c118 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-499949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log ((118 : ℕ)) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((118 : ℕ)) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7818319/10000000) (δ := 11331/1000000000) (ψ := -125063/500000) 449 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t118 : ((-9205271301/100000000000 : ℚ) : ℝ) ≤ stT449o2 118 := by
  have hc : ((-249987/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9205271301/100000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-249987/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c119 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((152267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log ((119 : ℕ)) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((119 : ℕ)) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -394171/1250000) (δ := 357/31250000) (ψ := -125063/500000) 449 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t119 : ((34889984229/1250000000000 : ℚ) : ℝ) ≤ stT449o2 119 := by
  have hc : ((76121/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34889984229/1250000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((76121/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c120 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((815423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log ((120 : ℕ)) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((120 : ℕ)) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1543341/10000000) (δ := 11279/1000000000) (ψ := -125063/500000) 449 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t120 : ((74432955051/1000000000000 : ℚ) : ℝ) ≤ stT449o2 120 := by
  have hc : ((815373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74432955051/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((815373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c121 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-789271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log ((121 : ℕ)) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((121 : ℕ)) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3100521/5000000) (δ := 5687/500000000) (ψ := -125063/500000) 449 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t121 : ((-717564617211/10000000000000 : ℚ) : ℝ) ≤ stT449o2 121 := by
  have hc : ((-789321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-717564617211/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-789321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c122 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-374841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log ((122 : ℕ)) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((122 : ℕ)) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4887553/10000000) (δ := 11317/1000000000) (ψ := -125063/500000) 449 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t122 : ((-169705282989/5000000000000 : ℚ) : ℝ) ≤ stT449o2 122 := by
  have hc : ((-374891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169705282989/5000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-374891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c123 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((992523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log ((123 : ℕ)) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((123 : ℕ)) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -305901/10000000) (δ := 11367/1000000000) (ψ := -125063/500000) 449 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t123 : ((894882137437/10000000000000 : ℚ) : ℝ) ≤ stT449o2 123 := by
  have hc : ((992473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((894882137437/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((992473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c124 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-62171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log ((124 : ℕ)) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((124 : ℕ)) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4238653/10000000) (δ := 5643/500000000) (ψ := -125063/500000) 449 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t124 : ((-13963421823/1250000000000 : ℚ) : ℝ) ≤ stT449o2 124 := by
  have hc : ((-15549/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13963421823/1250000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-15549/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c125 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-187383/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log ((125 : ℕ)) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((125 : ℕ)) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3480619/5000000) (δ := 5647/500000000) (ψ := -125063/500000) 449 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t125 : ((-41902386551/500000000000 : ℚ) : ℝ) ≤ stT449o2 125 := by
  have hc : ((-187393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41902386551/500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-187393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c126 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((543971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log ((126 : ℕ)) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((126 : ℕ)) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1244543/5000000) (δ := 11259/1000000000) (ψ := -125063/500000) 449 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t126 : ((48456290127/1000000000000 : ℚ) : ℝ) ≤ stT449o2 126 := by
  have hc : ((543921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48456290127/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((543921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c127 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((355787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log ((127 : ℕ)) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((127 : ℕ)) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1947651/10000000) (δ := 11409/1000000000) (ψ := -125063/500000) 449 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t127 : ((39460943159/625000000000 : ℚ) : ℝ) ≤ stT449o2 127 := by
  have hc : ((177881/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39460943159/625000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((177881/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c128 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-164871/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log ((128 : ℕ)) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((128 : ℕ)) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6349647/10000000) (δ := 11409/1000000000) (ψ := -125063/500000) 449 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t128 : ((-36433919451/500000000000 : ℚ) : ℝ) ≤ stT449o2 128 := by
  have hc : ((-164881/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36433919451/500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-164881/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c129 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-412709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log ((129 : ℕ)) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((129 : ℕ)) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1247639/2500000) (δ := 11251/1000000000) (ψ := -125063/500000) 449 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t129 : ((-363414074309/10000000000000 : ℚ) : ℝ) ≤ stT449o2 129 := by
  have hc : ((-412759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-363414074309/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-412759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c130 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((96571/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log ((130 : ℕ)) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((130 : ℕ)) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -82073/1250000) (δ := 5701/500000000) (ψ := -125063/500000) 449 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t130 : ((21173495707/250000000000 : ℚ) : ℝ) ≤ stT449o2 130 := by
  have hc : ((48283/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21173495707/250000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((48283/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c131 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((28217/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log ((131 : ℕ)) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((131 : ℕ)) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3644219/10000000) (δ := 2813/250000000) (ψ := -125063/500000) 449 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t131 : ((6160596117/625000000000 : ℚ) : ℝ) ≤ stT449o2 131 := by
  have hc : ((56409/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6160596117/625000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((56409/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c132 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-62483/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log ((132 : ℕ)) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((132 : ℕ)) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3897831/5000000) (δ := 713/62500000) (ψ := -125063/500000) 449 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t132 : ((-435097886821/5000000000000 : ℚ) : ℝ) ≤ stT449o2 132 := by
  have hc : ((-499889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-435097886821/5000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-499889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c133 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((2927/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log ((133 : ℕ)) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((133 : ℕ)) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -889949/2500000) (δ := 713/62500000) (ψ := -125063/500000) 449 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t133 : ((1268580467/100000000000 : ℚ) : ℝ) ≤ stT449o2 133 := by
  have hc : ((1463/10000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1268580467/100000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((1463/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c134 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((96697/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log ((134 : ℕ)) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((134 : ℕ)) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 644331/10000000) (δ := 5627/250000000) (ψ := -125063/500000) 449 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t134 : ((5220570291/62500000000 : ℚ) : ℝ) ≤ stT449o2 134 := by
  have hc : ((24173/25000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5220570291/62500000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((24173/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c135 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-69721/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log ((135 : ℕ)) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((135 : ℕ)) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4817197/10000000) (δ := 713/62500000) (ψ := -125063/500000) 449 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t135 : ((-60014891653/2000000000000 : ℚ) : ℝ) ≤ stT449o2 135 := by
  have hc : ((-69731/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60014891653/2000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-69731/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c136 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-903847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log ((136 : ℕ)) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((136 : ℕ)) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3374343/5000000) (δ := 2847/250000000) (ψ := -125063/500000) 449 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t136 : ((-775085350221/10000000000000 : ℚ) : ℝ) ≤ stT449o2 136 := by
  have hc : ((-903897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-775085350221/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-903897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c137 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((61679/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log ((137 : ℕ)) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((137 : ℕ)) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -164807/625000) (δ := 5619/500000000) (ψ := -125063/500000) 449 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t137 : ((210762182687/5000000000000 : ℚ) : ℝ) ≤ stT449o2 137 := by
  have hc : ((246691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210762182687/5000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((246691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c138 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((837581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log ((138 : ℕ)) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((138 : ℕ)) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1444891/10000000) (δ := 2253/200000000) (ψ := -125063/500000) 449 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t138 : ((89119161117/1250000000000 : ℚ) : ℝ) ≤ stT449o2 138 := by
  have hc : ((837531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89119161117/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((837531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c139 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-293811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log ((139 : ℕ)) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((139 : ℕ)) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1374321/2500000) (δ := 5669/500000000) (ψ := -125063/500000) 449 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t139 : ((-62307115751/1250000000000 : ℚ) : ℝ) ≤ stT449o2 139 := by
  have hc : ((-73459/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62307115751/1250000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-73459/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c140 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-392949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log ((140 : ℕ)) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((140 : ℕ)) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3093679/5000000) (δ := 2843/250000000) (ψ := -125063/500000) 449 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t140 : ((-33212394097/500000000000 : ℚ) : ℝ) ≤ stT449o2 140 := by
  have hc : ((-196487/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33212394097/500000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-196487/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c141 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((639393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log ((141 : ℕ)) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((141 : ℕ)) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1096359/5000000) (δ := 11381/1000000000) (ψ := -125063/500000) 449 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t141 : ((538423346793/10000000000000 : ℚ) : ℝ) ≤ stT449o2 141 := by
  have hc : ((639343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((538423346793/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((639343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c142 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((23709/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log ((142 : ℕ)) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((142 : ℕ)) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 443437/2500000) (δ := 11381/1000000000) (ψ := -125063/500000) 449 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t142 : ((318317297739/5000000000000 : ℚ) : ℝ) ≤ stT449o2 142 := by
  have hc : ((379319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((318317297739/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((379319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c143 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-327489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log ((143 : ℕ)) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((143 : ℕ)) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 714047/1250000) (δ := 11381/1000000000) (ψ := -125063/500000) 449 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t143 : ((-136940644951/2500000000000 : ℚ) : ℝ) ≤ stT449o2 143 := by
  have hc : ((-163757/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136940644951/2500000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-163757/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c144 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-189947/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log ((144 : ℕ)) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((144 : ℕ)) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -304223/500000) (δ := 11279/1000000000) (ψ := -125063/500000) 449 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t144 : ((-158299709973/2500000000000 : ℚ) : ℝ) ≤ stT449o2 144 := by
  have hc : ((-379919/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158299709973/2500000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-379919/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c145 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((637049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log ((145 : ℕ)) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((145 : ℕ)) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -220033/1000000) (δ := 357/31250000) (ψ := -125063/500000) 449 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t145 : ((264499183773/5000000000000 : ℚ) : ℝ) ≤ stT449o2 145 := by
  have hc : ((636999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264499183773/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((636999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c146 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((788251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log ((146 : ℕ)) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((146 : ℕ)) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 828543/5000000) (δ := 11379/1000000000) (ψ := -125063/500000) 449 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t146 : ((130463817721/2000000000000 : ℚ) : ℝ) ≤ stT449o2 146 := by
  have hc : ((788201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130463817721/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((788201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c147 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-584653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log ((147 : ℕ)) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((147 : ℕ)) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2744061/5000000) (δ := 11229/1000000000) (ψ := -125063/500000) 449 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t147 : ((-482255433261/10000000000000 : ℚ) : ℝ) ≤ stT449o2 147 := by
  have hc : ((-584703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-482255433261/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-584703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c148 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-209703/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log ((148 : ℕ)) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((148 : ℕ)) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1282947/2000000) (δ := 5683/500000000) (ψ := -125063/500000) 449 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t148 : ((-68954036969/1000000000000 : ℚ) : ℝ) ≤ stT449o2 148 := by
  have hc : ((-419431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68954036969/1000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-419431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c149 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((494021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log ((149 : ℕ)) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((149 : ℕ)) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2635221/10000000) (δ := 11237/1000000000) (ψ := -125063/500000) 449 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t149 : ((404676356301/10000000000000 : ℚ) : ℝ) ≤ stT449o2 149 := by
  have hc : ((493971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((404676356301/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((493971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c150 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((450751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log ((150 : ℕ)) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((150 : ℕ)) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 279731/2500000) (δ := 5633/500000000) (ψ := -125063/500000) 449 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t150 : ((11500499253/156250000000 : ℚ) : ℝ) ≤ stT449o2 150 := by
  have hc : ((225363/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11500499253/156250000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((225363/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c151 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-90051/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log ((151 : ℕ)) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((151 : ℕ)) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2424103/5000000) (δ := 11287/1000000000) (ψ := -125063/500000) 449 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t151 : ((-146585371203/5000000000000 : ℚ) : ℝ) ≤ stT449o2 151 := by
  have hc : ((-180127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146585371203/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-180127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c152 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-961181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log ((152 : ℕ)) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((152 : ℕ)) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1431023/2000000) (δ := 11409/1000000000) (ψ := -125063/500000) 449 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t152 : ((-194915538487/2500000000000 : ℚ) : ℝ) ≤ stT449o2 152 := by
  have hc : ((-961231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194915538487/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-961231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c153 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((89951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log ((153 : ℕ)) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((153 : ℕ)) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1737387/5000000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t153 : ((9087606819/625000000000 : ℚ) : ℝ) ≤ stT449o2 153 := by
  have hc : ((44963/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9087606819/625000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((44963/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c154 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((997363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log ((154 : ℕ)) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((154 : ℕ)) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 90801/5000000) (δ := 5697/500000000) (ψ := -125063/500000) 449 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t154 : ((401828378143/5000000000000 : ℚ) : ℝ) ≤ stT449o2 154 := by
  have hc : ((997313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((401828378143/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((997313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c155 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((5633/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log ((155 : ℕ)) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((155 : ℕ)) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 953573/2500000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t155 : ((18078050033/5000000000000 : ℚ) : ℝ) ≤ stT449o2 155 := by
  have hc : ((22507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18078050033/5000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((22507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c156 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-985221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log ((156 : ℕ)) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((156 : ℕ)) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1484727/2000000) (δ := 5647/500000000) (ψ := -125063/500000) 449 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t156 : ((-788848358711/10000000000000 : ℚ) : ℝ) ≤ stT449o2 156 := by
  have hc : ((-985271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-788848358711/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-985271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c157 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-151779/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log ((157 : ℕ)) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((157 : ℕ)) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4698053/10000000) (δ := 11301/1000000000) (ψ := -125063/500000) 449 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t157 : ((-30288199737/1250000000000 : ℚ) : ℝ) ≤ stT449o2 157 := by
  have hc : ((-37951/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30288199737/1250000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-37951/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c158 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((112347/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log ((158 : ℕ)) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((158 : ℕ)) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -226913/2000000) (δ := 1419/125000000) (ψ := -125063/500000) 449 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t158 : ((357493880191/5000000000000 : ℚ) : ℝ) ≤ stT449o2 158 := by
  have hc : ((449363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((357493880191/5000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((449363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c159 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((571397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log ((159 : ℕ)) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((159 : ℕ)) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1203237/5000000) (δ := 11301/1000000000) (ψ := -125063/500000) 449 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t159 : ((453107309697/10000000000000 : ℚ) : ℝ) ≤ stT449o2 159 := by
  have hc : ((571347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((453107309697/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((571347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c160 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-716881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log ((160 : ℕ)) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((160 : ℕ)) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5925287/10000000) (δ := 11301/1000000000) (ψ := -125063/500000) 449 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t160 : ((-56678414067/1000000000000 : ℚ) : ℝ) ≤ stT449o2 160 := by
  have hc : ((-716931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56678414067/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-716931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c161 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-809633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log ((161 : ℕ)) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((161 : ℕ)) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -392863/625000) (δ := 5679/500000000) (ψ := -125063/500000) 449 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t161 : ((-638120078813/10000000000000 : ℚ) : ℝ) ≤ stT449o2 161 := by
  have hc : ((-809683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-638120078813/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-809683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c162 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((431881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log ((162 : ℕ)) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((162 : ℕ)) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -702637/2500000) (δ := 5679/500000000) (ψ := -125063/500000) 449 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t162 : ((169639194547/5000000000000 : ℚ) : ℝ) ≤ stT449o2 162 := by
  have hc : ((431831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169639194547/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((431831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c163 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((967073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log ((163 : ℕ)) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((163 : ℕ)) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5026/78125) (δ := 2249/200000000) (ψ := -125063/500000) 449 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t163 : ((37871521749/500000000000 : ℚ) : ℝ) ≤ stT449o2 163 := by
  have hc : ((967023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37871521749/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((967023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c164 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-29793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log ((164 : ℕ)) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((164 : ℕ)) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 815209/2000000) (δ := 2269/200000000) (ψ := -125063/500000) 449 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t164 : ((-11641975921/2500000000000 : ℚ) : ℝ) ≤ stT449o2 164 := by
  have hc : ((-14909/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11641975921/2500000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-14909/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c165 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-989297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log ((165 : ℕ)) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((165 : ℕ)) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1871971/2500000) (δ := 2249/200000000) (ψ := -125063/500000) 449 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t165 : ((-770205650153/10000000000000 : ℚ) : ℝ) ≤ stT449o2 165 := by
  have hc : ((-989347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-770205650153/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-989347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c166 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-176483/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log ((166 : ℕ)) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((166 : ℕ)) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2414419/5000000) (δ := 2273/200000000) (ψ := -125063/500000) 449 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t166 : ((-34249215177/1250000000000 : ℚ) : ℝ) ≤ stT449o2 166 := by
  have hc : ((-44127/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34249215177/1250000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-44127/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c167 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((834723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log ((167 : ℕ)) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((167 : ℕ)) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -291583/2000000) (δ := 5669/500000000) (ψ := -125063/500000) 449 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t167 : ((645889164879/10000000000000 : ℚ) : ℝ) ≤ stT449o2 167 := by
  have hc : ((834673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((645889164879/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((834673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c168 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((22713/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log ((168 : ℕ)) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((168 : ℕ)) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 473201/2500000) (δ := 2253/200000000) (ψ := -125063/500000) 449 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t168 : ((70088949657/1250000000000 : ℚ) : ℝ) ≤ stT449o2 168 := by
  have hc : ((363383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70088949657/1250000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((363383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c169 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-495741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log ((169 : ℕ)) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((169 : ℕ)) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 522371/1000000) (δ := 2847/250000000) (ψ := -125063/500000) 449 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t169 : ((-381377806721/10000000000000 : ℚ) : ℝ) ≤ stT449o2 169 := by
  have hc : ((-495791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-381377806721/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-495791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c170 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-192627/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log ((170 : ℕ)) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((170 : ℕ)) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3586523/5000000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t170 : ((-29549167341/400000000000 : ℚ) : ℝ) ≤ stT449o2 170 := by
  have hc : ((-192637/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29549167341/400000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-192637/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c171 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((4573/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log ((171 : ℕ)) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((171 : ℕ)) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3881259/10000000) (δ := 141/12500000) (ψ := -125063/500000) 449 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t171 : ((6975001999/5000000000000 : ℚ) : ℝ) ≤ stT449o2 171 := by
  have hc : ((9121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6975001999/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((9121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c172 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((242627/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log ((172 : ℕ)) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((172 : ℕ)) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -304333/5000000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t172 : ((92495807667/1250000000000 : ℚ) : ℝ) ≤ stT449o2 172 := by
  have hc : ((485229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92495807667/1250000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((485229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c173 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((490631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log ((173 : ℕ)) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((173 : ℕ)) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 661239/2500000) (δ := 141/12500000) (ψ := -125063/500000) 449 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t173 : ((74596275117/2000000000000 : ℚ) : ℝ) ≤ stT449o2 173 := by
  have hc : ((490581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74596275117/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((490581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c174 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-704087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log ((174 : ℕ)) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((174 : ℕ)) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5879833/10000000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t174 : ((-533805555563/10000000000000 : ℚ) : ℝ) ≤ stT449o2 174 := by
  have hc : ((-704137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-533805555563/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-704137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c175 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-879073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log ((175 : ℕ)) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((175 : ℕ)) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -264471/400000) (δ := 141/12500000) (ψ := -125063/500000) 449 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t175 : ((-664554570267/10000000000000 : ℚ) : ℝ) ≤ stT449o2 175 := by
  have hc : ((-879123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-664554570267/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-879123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c176 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((25481/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log ((176 : ℕ)) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((176 : ℕ)) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3413773/10000000) (δ := 11373/1000000000) (ψ := -125063/500000) 449 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t176 : ((38404612211/2500000000000 : ℚ) : ℝ) ≤ stT449o2 176 := by
  have hc : ((101899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38404612211/2500000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((101899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c177 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((995629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log ((177 : ℕ)) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((177 : ℕ)) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -116921/5000000) (δ := 569/50000000) (ψ := -125063/500000) 449 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t177 : ((374161486517/5000000000000 : ℚ) : ℝ) ≤ stT449o2 177 := by
  have hc : ((995579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((374161486517/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((995579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c178 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((388999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log ((178 : ℕ)) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((178 : ℕ)) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 22876/78125) (δ := 141/12500000) (ψ := -125063/500000) 449 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t178 : ((291529332919/10000000000000 : ℚ) : ℝ) ≤ stT449o2 178 := by
  have hc : ((388949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291529332919/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((388949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c179 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-94581/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log ((179 : ℕ)) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((179 : ℕ)) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6072419/10000000) (δ := 1133/100000000) (ψ := -125063/500000) 449 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t179 : ((-70697915791/1250000000000 : ℚ) : ℝ) ≤ stT449o2 179 := by
  have hc : ((-378349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70697915791/1250000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-378349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c180 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-429351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log ((180 : ℕ)) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((180 : ℕ)) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6508821/10000000) (δ := 2829/250000000) (ψ := -125063/500000) 449 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t180 : ((-1250148351/19531250000 : ℚ) : ℝ) ≤ stT449o2 180 := by
  have hc : ((-13418/15625 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1250148351/19531250000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-13418/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c181 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((5237/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log ((181 : ℕ)) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((181 : ℕ)) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -424923/1250000) (δ := 1427/125000000) (ψ := -125063/500000) 449 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t181 : ((7783403121/500000000000 : ℚ) : ℝ) ≤ stT449o2 181 := by
  have hc : ((20943/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7783403121/500000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((20943/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c182 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((62029/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log ((182 : ℕ)) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((182 : ℕ)) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -307121/10000000) (δ := 1427/125000000) (ψ := -125063/500000) 449 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t182 : ((367812942543/5000000000000 : ℚ) : ℝ) ≤ stT449o2 182 := by
  have hc : ((496207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((367812942543/5000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((496207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c183 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((447079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log ((183 : ℕ)) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((183 : ℕ)) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2768249/10000000) (δ := 11287/1000000000) (ψ := -125063/500000) 449 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t183 : ((330453224409/10000000000000 : ℚ) : ℝ) ≤ stT449o2 183 := by
  have hc : ((447029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330453224409/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((447029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c184 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-688877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log ((184 : ℕ)) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((184 : ℕ)) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5826837/10000000) (δ := 11287/1000000000) (ψ := -125063/500000) 449 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t184 : ((-50788387367/1000000000000 : ℚ) : ℝ) ≤ stT449o2 184 := by
  have hc : ((-688927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50788387367/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-688927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c185 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-459363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log ((185 : ℕ)) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((185 : ℕ)) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1367819/2000000) (δ := 709/62500000) (ψ := -125063/500000) 449 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t185 : ((-16887447421/250000000000 : ℚ) : ℝ) ≤ stT449o2 185 := by
  have hc : ((-114847/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16887447421/250000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-114847/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c186 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((45377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log ((186 : ℕ)) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((186 : ℕ)) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3813509/10000000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t186 : ((6647068569/2000000000000 : ℚ) : ℝ) ≤ stT449o2 186 := by
  have hc : ((45327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6647068569/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((45327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c187 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((11859/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log ((187 : ℕ)) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((187 : ℕ)) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -402043/5000000) (δ := 709/62500000) (ψ := -125063/500000) 449 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t187 : ((8671697603/125000000000 : ℚ) : ℝ) ≤ stT449o2 187 := by
  have hc : ((94867/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8671697603/125000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((94867/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c188 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((320233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log ((188 : ℕ)) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((188 : ℕ)) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 547307/2500000) (δ := 11359/1000000000) (ψ := -125063/500000) 449 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t188 : ((3648990303/78125000000 : ℚ) : ℝ) ≤ stT449o2 188 := by
  have hc : ((20013/31250 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3648990303/78125000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((20013/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c189 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-95163/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log ((189 : ℕ)) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((189 : ℕ)) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1291679/2500000) (δ := 709/62500000) (ψ := -125063/500000) 449 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t189 : ((-69228173989/2000000000000 : ℚ) : ℝ) ≤ stT449o2 189 := by
  have hc : ((-95173/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69228173989/2000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-95173/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c190 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-49699/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log ((190 : ℕ)) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((190 : ℕ)) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7579531/10000000) (δ := 11351/1000000000) (ψ := -125063/500000) 449 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t190 : ((-72114590231/1000000000000 : ℚ) : ℝ) ≤ stT449o2 190 := by
  have hc : ((-99403/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72114590231/1000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-99403/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c191 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-139391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log ((191 : ℕ)) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((191 : ℕ)) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2316653/5000000) (δ := 5701/500000000) (ψ := -125063/500000) 449 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t191 : ((-504389661/25000000000 : ℚ) : ℝ) ≤ stT449o2 191 := by
  have hc : ((-17427/62500 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-504389661/25000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-17427/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c192 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((38847/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log ((192 : ℕ)) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((192 : ℕ)) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -851257/5000000) (δ := 11301/1000000000) (ψ := -125063/500000) 449 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t192 : ((56067141343/1000000000000 : ℚ) : ℝ) ≤ stT449o2 192 := by
  have hc : ((77689/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56067141343/1000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((77689/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c193 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((884569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log ((193 : ℕ)) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((193 : ℕ)) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1213067/10000000) (δ := 1419/125000000) (ψ := -125063/500000) 449 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t193 : ((127338008797/2000000000000 : ℚ) : ℝ) ≤ stT449o2 193 := by
  have hc : ((884519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127338008797/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((884519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c194 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-74577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log ((194 : ℕ)) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((194 : ℕ)) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4113607/10000000) (δ := 1419/125000000) (ψ := -125063/500000) 449 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t194 : ((-53579126293/10000000000000 : ℚ) : ℝ) ≤ stT449o2 194 := by
  have hc : ((-74627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53579126293/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-74627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c195 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-471059/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log ((195 : ℕ)) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((195 : ℕ)) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3499609/5000000) (δ := 2813/250000000) (ψ := -125063/500000) 449 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t195 : ((-16867515933/250000000000 : ℚ) : ℝ) ≤ stT449o2 195 := by
  have hc : ((-117771/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16867515933/250000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-117771/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c196 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-173019/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log ((196 : ℕ)) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((196 : ℕ)) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1167579/2000000) (δ := 5679/500000000) (ψ := -125063/500000) 449 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t196 : ((-123593978009/2500000000000 : ℚ) : ℝ) ≤ stT449o2 196 := by
  have hc : ((-346063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123593978009/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-346063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c197 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((184597/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log ((197 : ℕ)) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((197 : ℕ)) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1490819/5000000) (δ := 2249/200000000) (ψ := -125063/500000) 449 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t197 : ((3287550321/125000000000 : ℚ) : ℝ) ≤ stT449o2 197 := by
  have hc : ((46143/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3287550321/125000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((46143/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c198 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((249609/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log ((198 : ℕ)) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((198 : ℕ)) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -139861/10000000) (δ := 2259/200000000) (ψ := -125063/500000) 449 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t198 : ((354760990117/5000000000000 : ℚ) : ℝ) ≤ stT449o2 198 := by
  have hc : ((499193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((354760990117/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((499193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c199 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((29731/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log ((199 : ℕ)) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((199 : ℕ)) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 671901/2500000) (δ := 2279/200000000) (ψ := -125063/500000) 449 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t199 : ((168588206063/5000000000000 : ℚ) : ℝ) ≤ stT449o2 199 := by
  have hc : ((237823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168588206063/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((237823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c200 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-294391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log ((200 : ℕ)) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((200 : ℕ)) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 550087/1000000) (δ := 2249/200000000) (ψ := -125063/500000) 449 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t200 : ((-13011475907/312500000000 : ℚ) : ℝ) ≤ stT449o2 200 := by
  have hc : ((-18401/31250 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13011475907/312500000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-18401/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c201 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-246029/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log ((201 : ℕ)) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((201 : ℕ)) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7407803/10000000) (δ := 11337/1000000000) (ψ := -125063/500000) 449 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t201 : ((-173544387859/2500000000000 : ℚ) : ℝ) ≤ stT449o2 201 := by
  have hc : ((-492083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173544387859/2500000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-492083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c202 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-4291/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log ((202 : ℕ)) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((202 : ℕ)) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4622487/10000000) (δ := 5683/500000000) (ψ := -125063/500000) 449 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t202 : ((-48315019263/2500000000000 : ℚ) : ℝ) ≤ stT449o2 202 := by
  have hc : ((-137337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48315019263/2500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-137337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c203 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((147647/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log ((203 : ℕ)) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((203 : ℕ)) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -925433/5000000) (δ := 1427/125000000) (ψ := -125063/500000) 449 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t203 : ((51810400047/1000000000000 : ℚ) : ℝ) ≤ stT449o2 203 := by
  have hc : ((147637/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51810400047/1000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((147637/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c204 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((93489/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log ((204 : ℕ)) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((204 : ℕ)) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 226779/2500000) (δ := 11237/1000000000) (ψ := -125063/500000) 449 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t204 : ((818148597/12500000000 : ℚ) : ℝ) ≤ stT449o2 204 := by
  have hc : ((23371/25000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((818148597/12500000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((23371/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c205 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((54961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log ((205 : ℕ)) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((205 : ℕ)) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3651629/10000000) (δ := 1427/125000000) (ψ := -125063/500000) 449 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t205 : ((479611881/62500000000 : ℚ) : ℝ) ≤ stT449o2 205 := by
  have hc : ((6867/62500 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((479611881/62500000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((6867/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c206 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-415893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log ((206 : ℕ)) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((206 : ℕ)) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6382783/10000000) (δ := 11337/1000000000) (ψ := -125063/500000) 449 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t206 : ((-72446052953/1250000000000 : ℚ) : ℝ) ≤ stT449o2 206 := by
  have hc : ((-207959/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72446052953/1250000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-207959/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c207 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-878213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log ((207 : ℕ)) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((207 : ℕ)) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6607271/10000000) (δ := 1133/100000000) (ψ := -125063/500000) 449 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t207 : ((-610435819887/10000000000000 : ℚ) : ℝ) ≤ stT449o2 207 := by
  have hc : ((-878263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-610435819887/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-878263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c208 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((9821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log ((208 : ℕ)) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((208 : ℕ)) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3902439/10000000) (δ := 569/50000000) (ψ := -125063/500000) 449 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t208 : ((54199737/80000000000 : ℚ) : ℝ) ≤ stT449o2 208 := by
  have hc : ((9771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54199737/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((9771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c209 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((442517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log ((209 : ℕ)) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((209 : ℕ)) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1210571/10000000) (δ := 11373/1000000000) (ψ := -125063/500000) 449 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t209 : ((38259738911/625000000000 : ℚ) : ℝ) ≤ stT449o2 209 := by
  have hc : ((110623/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38259738911/625000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((110623/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c210 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((832397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log ((210 : ℕ)) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((210 : ℕ)) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1468443/10000000) (δ := 1133/100000000) (ψ := -125063/500000) 449 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t210 : ((114874706511/2000000000000 : ℚ) : ℝ) ≤ stT449o2 210 := by
  have hc : ((832347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114874706511/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((832347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c211 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-16599/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log ((211 : ℕ)) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((211 : ℕ)) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2067359/5000000) (δ := 11423/1000000000) (ψ := -125063/500000) 449 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t211 : ((-11434117261/2000000000000 : ℚ) : ℝ) ≤ stT449o2 211 := by
  have hc : ((-16609/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11434117261/2000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-16609/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c212 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-227631/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log ((212 : ℕ)) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((212 : ℕ)) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1697091/2500000) (δ := 11373/1000000000) (ψ := -125063/500000) 449 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t212 : ((-312692477461/5000000000000 : ℚ) : ℝ) ≤ stT449o2 212 := by
  have hc : ((-455287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-312692477461/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-455287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c213 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-807893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log ((213 : ℕ)) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((213 : ℕ)) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6278413/10000000) (δ := 1133/100000000) (ψ := -125063/500000) 449 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t213 : ((-553593656227/10000000000000 : ℚ) : ℝ) ≤ stT449o2 213 := by
  have hc : ((-807943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-553593656227/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-807943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c214 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((110739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log ((214 : ℕ)) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((214 : ℕ)) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1824787/5000000) (δ := 569/50000000) (ψ := -125063/500000) 449 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t214 : ((15133068013/2000000000000 : ℚ) : ℝ) ≤ stT449o2 214 := by
  have hc : ((110689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15133068013/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((110689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c215 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((228959/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log ((215 : ℕ)) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((215 : ℕ)) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1033027/10000000) (δ := 11273/1000000000) (ψ := -125063/500000) 449 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t215 : ((156140139321/2500000000000 : ℚ) : ℝ) ≤ stT449o2 215 := by
  have hc : ((457893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156140139321/2500000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((457893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c216 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((202219/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log ((216 : ℕ)) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((216 : ℕ)) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 785699/5000000) (δ := 569/50000000) (ψ := -125063/500000) 449 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t216 : ((275167862569/5000000000000 : ℚ) : ℝ) ≤ stT449o2 216 := by
  have hc : ((404413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((275167862569/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((404413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c217 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-23641/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log ((217 : ℕ)) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((217 : ℕ)) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 832751/2000000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t217 : ((-6422824083/1000000000000 : ℚ) : ℝ) ≤ stT449o2 217 := by
  have hc : ((-47307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6422824083/1000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-47307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c218 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-903081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log ((218 : ℕ)) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((218 : ℕ)) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3372107/5000000) (δ := 11373/1000000000) (ψ := -125063/500000) 449 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t218 : ((-305838991233/5000000000000 : ℚ) : ℝ) ≤ stT449o2 218 := by
  have hc : ((-903131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305838991233/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-903131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c219 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-166901/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log ((219 : ℕ)) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((219 : ℕ)) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1598769/2500000) (δ := 11237/1000000000) (ψ := -125063/500000) 449 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t219 : ((-56394052659/1000000000000 : ℚ) : ℝ) ≤ stT449o2 219 := by
  have hc : ((-166911/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56394052659/1000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-166911/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c220 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((2221/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log ((220 : ℕ)) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((220 : ℕ)) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3838133/10000000) (δ := 11337/1000000000) (ψ := -125063/500000) 449 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t220 : ((11962312857/5000000000000 : ℚ) : ℝ) ≤ stT449o2 220 := by
  have hc : ((17743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11962312857/5000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((17743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c221 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((108657/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log ((221 : ℕ)) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((221 : ℕ)) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -80797/625000) (δ := 11337/1000000000) (ψ := -125063/500000) 449 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t221 : ((9135789663/156250000000 : ℚ) : ℝ) ≤ stT449o2 221 := by
  have hc : ((434603/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9135789663/156250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((434603/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c222 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((87929/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log ((222 : ℕ)) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((222 : ℕ)) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1241067/10000000) (δ := 11237/1000000000) (ψ := -125063/500000) 449 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t222 : ((3688170009/62500000000 : ℚ) : ℝ) ≤ stT449o2 222 := by
  have hc : ((21981/25000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3688170009/62500000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((21981/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c223 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((6533/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log ((223 : ℕ)) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((223 : ℕ)) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3763549/10000000) (δ := 11237/1000000000) (ψ := -125063/500000) 449 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t223 : ((34152099/7812500000 : ℚ) : ℝ) ≤ stT449o2 223 := by
  have hc : ((204/3125 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34152099/7812500000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((204/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c224 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-807029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log ((224 : ℕ)) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((224 : ℕ)) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 25099/40000) (δ := 11287/1000000000) (ψ := -125063/500000) 449 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t224 : ((-269626531083/5000000000000 : ℚ) : ℝ) ≤ stT449o2 224 := by
  have hc : ((-807079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269626531083/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-807079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c225 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-932933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log ((225 : ℕ)) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((225 : ℕ)) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6933181/10000000) (δ := 5697/500000000) (ψ := -125063/500000) 449 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t225 : ((-621988977661/10000000000000 : ℚ) : ℝ) ≤ stT449o2 225 := by
  have hc : ((-932983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-621988977661/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-932983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c226 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-102723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log ((226 : ℕ)) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((226 : ℕ)) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -444429/1000000) (δ := 1409/62500000) (ψ := -125063/500000) 449 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t226 : ((-17086761217/1250000000000 : ℚ) : ℝ) ≤ stT449o2 226 := by
  have hc : ((-25687/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17086761217/1250000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-25687/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c227 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((706301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log ((227 : ℕ)) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((227 : ℕ)) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1966343/10000000) (δ := 5697/500000000) (ψ := -125063/500000) 449 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t227 : ((468755032473/10000000000000 : ℚ) : ℝ) ≤ stT449o2 227 := by
  have hc : ((706251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((468755032473/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((706251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c228 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((245003/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log ((228 : ℕ)) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((228 : ℕ)) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 500687/10000000) (δ := 11259/1000000000) (ψ := -125063/500000) 449 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t228 : ((162248878473/2500000000000 : ℚ) : ℝ) ≤ stT449o2 228 := by
  have hc : ((489981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162248878473/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((489981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c229 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((94589/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log ((229 : ℕ)) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((229 : ℕ)) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1478471/5000000) (δ := 5697/500000000) (ψ := -125063/500000) 449 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t229 : ((62497853577/2500000000000 : ℚ) : ℝ) ≤ stT449o2 229 := by
  have hc : ((189153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62497853577/2500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((189153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c230 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-278261/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log ((230 : ℕ)) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((230 : ℕ)) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1350619/2500000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t230 : ((-91748250483/2500000000000 : ℚ) : ℝ) ≤ stT449o2 230 := by
  have hc : ((-139143/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91748250483/2500000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-139143/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c231 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-499989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log ((231 : ℕ)) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((231 : ℕ)) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7837403/10000000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t231 : ((-5140393927/78125000000 : ℚ) : ℝ) ≤ stT449o2 231 := by
  have hc : ((-250007/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5140393927/78125000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-250007/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c232 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-285481/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log ((232 : ℕ)) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((232 : ℕ)) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1089237/2000000) (δ := 11401/1000000000) (ψ := -125063/500000) 449 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t232 : ((-93722055349/2500000000000 : ℚ) : ℝ) ≤ stT449o2 232 := by
  have hc : ((-142753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93722055349/2500000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-142753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c233 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((175163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log ((233 : ℕ)) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((233 : ℕ)) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -23689/78125) (δ := 5651/500000000) (ψ := -125063/500000) 449 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t233 : ((57368290849/2500000000000 : ℚ) : ℝ) ≤ stT449o2 233 := by
  have hc : ((87569/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57368290849/2500000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((87569/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c234 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((484281/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log ((234 : ℕ)) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((234 : ℕ)) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -628527/10000000) (δ := 11301/1000000000) (ψ := -125063/500000) 449 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t234 : ((247318619/3906250000 : ℚ) : ℝ) ≤ stT449o2 234 := by
  have hc : ((15133/15625 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247318619/3906250000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((15133/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c235 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((760997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log ((235 : ℕ)) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((235 : ℕ)) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 441217/2500000) (δ := 1419/125000000) (ψ := -125063/500000) 449 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t235 : ((62048379327/1250000000000 : ℚ) : ℝ) ≤ stT449o2 235 := by
  have hc : ((760947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62048379327/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((760947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c236 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-8833/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log ((236 : ℕ)) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((236 : ℕ)) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 518513/1250000) (δ := 5701/500000000) (ψ := -125063/500000) 449 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t236 : ((-575305191/100000000000 : ℚ) : ℝ) ≤ stT449o2 236 := by
  have hc : ((-4419/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-575305191/100000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-4419/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c237 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-861237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log ((237 : ℕ)) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((237 : ℕ)) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6521237/10000000) (δ := 2813/250000000) (ψ := -125063/500000) 449 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t237 : ((-55946619659/1000000000000 : ℚ) : ℝ) ≤ stT449o2 237 := by
  have hc : ((-861287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55946619659/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-861287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c238 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-458129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log ((238 : ℕ)) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((238 : ℕ)) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6823583/10000000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 196
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t238 : ((-37122156927/625000000000 : ℚ) : ℝ) ≤ stT449o2 238 := by
  have hc : ((-229077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37122156927/625000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-229077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c239 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-26953/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log ((239 : ℕ)) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((239 : ℕ)) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2235159/5000000) (δ := 11259/1000000000) (ψ := -125063/500000) 449 196
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t239 : ((-69754039939/5000000000000 : ℚ) : ℝ) ≤ stT449o2 239 := by
  have hc : ((-107837/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69754039939/5000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-107837/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c240 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((32971/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log ((240 : ℕ)) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((240 : ℕ)) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3403/16000) (δ := 5647/500000000) (ψ := -125063/500000) 449 196
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t240 : ((42562135689/1000000000000 : ℚ) : ℝ) ≤ stT449o2 240 := by
  have hc : ((65937/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42562135689/1000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((65937/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c241 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((996581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log ((241 : ℕ)) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((241 : ℕ)) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 206803/10000000) (δ := 11359/1000000000) (ψ := -125063/500000) 449 196
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t241 : ((160480355709/2500000000000 : ℚ) : ℝ) ≤ stT449o2 241 := by
  have hc : ((996531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160480355709/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((996531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c242 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((105977/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log ((242 : ℕ)) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((242 : ℕ)) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2530827/10000000) (δ := 11359/1000000000) (ψ := -125063/500000) 449 196
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t242 : ((8514766351/250000000000 : ℚ) : ℝ) ≤ stT449o2 242 := by
  have hc : ((105967/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8514766351/250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((105967/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c243 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-359101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log ((243 : ℕ)) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((243 : ℕ)) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4845253/10000000) (δ := 709/62500000) (ψ := -125063/500000) 449 196
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t243 : ((-230395725651/10000000000000 : ℚ) : ℝ) ≤ stT449o2 243 := by
  have hc : ((-359151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230395725651/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-359151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c244 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-240159/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log ((244 : ℕ)) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((244 : ℕ)) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1430039/2000000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 196
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t244 : ((-61501676691/1000000000000 : ℚ) : ℝ) ≤ stT449o2 244 := by
  have hc : ((-480343/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61501676691/1000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-480343/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c245 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-32163/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log ((245 : ℕ)) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((245 : ℕ)) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1565571/2500000) (δ := 11233/500000000) (ψ := -125063/500000) 449 197
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t245 : ((-4109895741/80000000000 : ℚ) : ℝ) ≤ stT449o2 245 := by
  have hc : ((-6433/8000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4109895741/80000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-6433/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c246 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-19649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log ((246 : ℕ)) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((246 : ℕ)) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -994029/2500000) (δ := 5683/500000000) (ψ := -125063/500000) 449 197
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t246 : ((-12559629323/10000000000000 : ℚ) : ℝ) ≤ stT449o2 246 := by
  have hc : ((-19699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12559629323/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-19699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c247 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((155553/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log ((247 : ℕ)) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((247 : ℕ)) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1699237/10000000) (δ := 5683/500000000) (ψ := -125063/500000) 449 197
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t247 : ((24742380553/500000000000 : ℚ) : ℝ) ≤ stT449o2 247 := by
  have hc : ((155543/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24742380553/500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((155543/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c248 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((487131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log ((248 : ℕ)) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((248 : ℕ)) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 568437/10000000) (δ := 11287/1000000000) (ψ := -125063/500000) 449 197
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t248 : ((30931231/500000000 : ℚ) : ℝ) ≤ stT449o2 248 := by
  have hc : ((243553/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30931231/500000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((243553/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c249 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((8519/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log ((249 : ℕ)) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((249 : ℕ)) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2826963/10000000) (δ := 11337/1000000000) (ψ := -125063/500000) 449 197
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t249 : ((674757629/25000000000 : ℚ) : ℝ) ≤ stT449o2 249 := by
  have hc : ((4259/10000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((674757629/25000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((4259/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c250 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-17751/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log ((250 : ℕ)) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((250 : ℕ)) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5076509/10000000) (δ := 11387/1000000000) (ψ := -125063/500000) 449 197
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t250 : ((-1403498921/50000000000 : ℚ) : ℝ) ≤ stT449o2 250 := by
  have hc : ((-17753/40000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1403498921/50000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-17753/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c251 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((251 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-488511/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55254529/20000000 : ℚ) : ℝ) ≤ Real.log ((251 : ℕ)) / 2 := by
    have h := (log_br_251).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((251 : ℕ)) / 2 ≤ ((5525453/2000000 : ℚ) : ℝ) := by
    have h := (log_br_251).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7317019/10000000) (δ := 11387/1000000000) (ψ := -125063/500000) 449 197
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t251 : ((-7709037013/125000000000 : ℚ) : ℝ) ≤ stT449o2 251 := by
  have hc : ((-61067/62500 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((251 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7709037013/125000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-61067/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c252 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((252 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-778923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5529429/2000000 : ℚ) : ℝ) ≤ Real.log ((252 : ℕ)) / 2 := by
    have h := (log_br_252).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((252 : ℕ)) / 2 ≤ ((55294291/20000000 : ℚ) : ℝ) := by
    have h := (log_br_252).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3079679/5000000) (δ := 1133/100000000) (ψ := -125063/500000) 449 198
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t252 : ((-490707030593/10000000000000 : ℚ) : ℝ) ≤ stT449o2 252 := by
  have hc : ((-778973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((252 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-490707030593/10000000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-778973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c253 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((253 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-3837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27666947/10000000 : ℚ) : ℝ) ≤ Real.log ((253 : ℕ)) / 2 := by
    have h := (log_br_253).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((253 : ℕ)) / 2 ≤ ((11066779/4000000 : ℚ) : ℝ) := by
    have h := (log_br_253).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3936583/10000000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 198
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t253 : ((-488747493/2000000000000 : ℚ) : ℝ) ≤ stT449o2 253 := by
  have hc : ((-3887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((253 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-488747493/2000000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-3887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c254 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((254 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((385933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27686671/10000000 : ℚ) : ℝ) ≤ Real.log ((254 : ℕ)) / 2 := by
    have h := (log_br_254).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((254 : ℕ)) / 2 ≤ ((55373343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_254).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -430641/2500000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 198
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t254 : ((12106995207/250000000000 : ℚ) : ℝ) ≤ stT449o2 254 := by
  have hc : ((96477/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((254 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).1
  have hw2 : ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((125491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12106995207/250000000000 : ℚ) : ℝ)
      = ((125491/2000000 : ℚ) : ℝ) * ((96477/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c255 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((255 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((490707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11082527/4000000 : ℚ) : ℝ) ≤ Real.log ((255 : ℕ)) / 2 := by
    have h := (log_br_255).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((255 : ℕ)) / 2 ≤ ((13853159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_255).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 96551/2000000) (δ := 569/50000000) (ψ := -125063/500000) 449 198
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t255 : ((9602401399/156250000000 : ℚ) : ℝ) ≤ stT449o2 255 := by
  have hc : ((245341/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((255 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).1
  have hw2 : ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39139/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9602401399/156250000000 : ℚ) : ℝ)
      = ((39139/625000 : ℚ) : ℝ) * ((245341/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c256 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((256 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((59821/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27725887/10000000 : ℚ) : ℝ) ≤ Real.log ((256 : ℕ)) / 2 := by
    have h := (log_br_256).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((256 : ℕ)) / 2 ≤ ((2218071/800000 : ℚ) : ℝ) := by
    have h := (log_br_256).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 334929/1250000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 198
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t256 : ((239259/8000000 : ℚ) : ℝ) ≤ stT449o2 256 := by
  have hc : ((239259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((256 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239259/8000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((239259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c257 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((257 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-1837/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1387269/500000 : ℚ) : ℝ) ≤ Real.log ((257 : ℕ)) / 2 := by
    have h := (log_br_257).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((257 : ℕ)) / 2 ≤ ((55490761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_257).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4867521/10000000) (δ := 1123/100000000) (ψ := -125063/500000) 449 198
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t257 : ((-4584181267/200000000000 : ℚ) : ℝ) ≤ stT449o2 257 := by
  have hc : ((-7349/20000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((257 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).2
  have h0 : (0:ℝ) ≤ ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4584181267/200000000000 : ℚ) : ℝ)
      = ((623783/10000000 : ℚ) : ℝ) * ((-7349/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c258 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((258 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-94837/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11105919/4000000 : ℚ) : ℝ) ≤ Real.log ((258 : ℕ)) / 2 := by
    have h := (log_br_258).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((258 : ℕ)) / 2 ≤ ((13882399/5000000 : ℚ) : ℝ) := by
    have h := (log_br_258).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1409427/2000000) (δ := 569/50000000) (ψ := -125063/500000) 449 198
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t258 : ((-29523034233/500000000000 : ℚ) : ℝ) ≤ stT449o2 258 := by
  have hc : ((-47421/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((258 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).2
  have h0 : (0:ℝ) ≤ ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29523034233/500000000000 : ℚ) : ℝ)
      = ((622573/10000000 : ℚ) : ℝ) * ((-47421/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c259 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((259 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-106843/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1389207/500000 : ℚ) : ℝ) ≤ Real.log ((259 : ℕ)) / 2 := by
    have h := (log_br_259).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((259 : ℕ)) / 2 ≤ ((55568281/20000000 : ℚ) : ℝ) := by
    have h := (log_br_259).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -202801/312500) (δ := 1133/100000000) (ψ := -125063/500000) 449 199
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t259 : ((-26557167389/500000000000 : ℚ) : ℝ) ≤ stT449o2 259 := by
  have hc : ((-427397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((259 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26557167389/500000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-427397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c260 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((260 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-79621/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1737713/625000 : ℚ) : ℝ) ≤ Real.log ((260 : ℕ)) / 2 := by
    have h := (log_br_260).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((260 : ℕ)) / 2 ≤ ((55606817/20000000 : ℚ) : ℝ) := by
    have h := (log_br_260).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4326799/10000000) (δ := 1133/100000000) (ψ := -125063/500000) 449 199
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t260 : ((-12348594601/1250000000000 : ℚ) : ℝ) ≤ stT449o2 260 := by
  have hc : ((-39823/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((260 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12348594601/1250000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-39823/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c261 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((261 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((32283/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13911301/5000000 : ℚ) : ℝ) ≤ Real.log ((261 : ℕ)) / 2 := by
    have h := (log_br_261).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((261 : ℕ)) / 2 ≤ ((11129041/4000000 : ℚ) : ℝ) := by
    have h := (log_br_261).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2172273/10000000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 199
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t261 : ((4995278253/125000000000 : ℚ) : ℝ) ≤ stT449o2 261 := by
  have hc : ((64561/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((261 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).1
  have hw2 : ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((77373/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4995278253/125000000000 : ℚ) : ℝ)
      = ((77373/1250000 : ℚ) : ℝ) * ((64561/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c262 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((262 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((499973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13920861/5000000 : ℚ) : ℝ) ≤ Real.log ((262 : ℕ)) / 2 := by
    have h := (log_br_262).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((262 : ℕ)) / 2 ≤ ((55683447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_262).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -25997/10000000) (δ := 33823/1000000000) (ψ := -125063/500000) 449 199
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t262 : ((38608609287/625000000000 : ℚ) : ℝ) ≤ stT449o2 262 := by
  have hc : ((124987/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((262 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).1
  have hw2 : ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38608609287/625000000000 : ℚ) : ℝ)
      = ((308901/5000000 : ℚ) : ℝ) * ((124987/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c263 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((263 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((132771/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2786077/1000000 : ℚ) : ℝ) ≤ Real.log ((263 : ℕ)) / 2 := by
    have h := (log_br_263).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((263 : ℕ)) / 2 ≤ ((55721541/20000000 : ℚ) : ℝ) := by
    have h := (log_br_263).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 422417/2000000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 199
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t263 : ((40931942193/1000000000000 : ℚ) : ℝ) ≤ stT449o2 263 := by
  have hc : ((132761/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((263 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40931942193/1000000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((132761/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c264 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((264 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-15713/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5575949/2000000 : ℚ) : ℝ) ≤ Real.log ((264 : ℕ)) / 2 := by
    have h := (log_br_264).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((264 : ℕ)) / 2 ≤ ((55759493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_264).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 848417/2000000) (δ := 33723/1000000000) (ψ := -125063/500000) 449 199
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t264 : ((-19349076333/2500000000000 : ℚ) : ℝ) ≤ stT449o2 264 := by
  have hc : ((-62877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((264 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).2
  have h0 : (0:ℝ) ≤ ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19349076333/2500000000000 : ℚ) : ℝ)
      = ((307729/5000000 : ℚ) : ℝ) * ((-62877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c265 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((265 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-103449/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27898649/10000000 : ℚ) : ℝ) ≤ Real.log ((265 : ℕ)) / 2 := by
    have h := (log_br_265).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((265 : ℕ)) / 2 ≤ ((55797299/20000000 : ℚ) : ℝ) := by
    have h := (log_br_265).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6364003/10000000) (δ := 1123/100000000) (ψ := -125063/500000) 449 199
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t265 : ((-31776073127/625000000000 : ℚ) : ℝ) ≤ stT449o2 265 := by
  have hc : ((-413821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((265 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).2
  have h0 : (0:ℝ) ≤ ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31776073127/625000000000 : ℚ) : ℝ)
      = ((76787/1250000 : ℚ) : ℝ) * ((-413821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c266 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((266 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-484507/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55834963/20000000 : ℚ) : ℝ) ≤ Real.log ((266 : ℕ)) / 2 := by
    have h := (log_br_266).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((266 : ℕ)) / 2 ≤ ((13958741/5000000 : ℚ) : ℝ) := by
    have h := (log_br_266).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1807503/2500000) (δ := 11287/1000000000) (ψ := -125063/500000) 449 200
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t266 : ((-3713574381/62500000000 : ℚ) : ℝ) ≤ stT449o2 266 := by
  have hc : ((-121133/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((266 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3713574381/62500000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-121133/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c267 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((267 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-46073/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27936243/10000000 : ℚ) : ℝ) ≤ Real.log ((267 : ℕ)) / 2 := by
    have h := (log_br_267).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((267 : ℕ)) / 2 ≤ ((55872487/20000000 : ℚ) : ℝ) := by
    have h := (log_br_267).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2562017/5000000) (δ := 2829/250000000) (ψ := -125063/500000) 449 200
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t267 : ((-14099660649/500000000000 : ℚ) : ℝ) ≤ stT449o2 267 := by
  have hc : ((-23039/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((267 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14099660649/500000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-23039/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c268 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((268 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((176339/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55909869/20000000 : ℚ) : ℝ) ≤ Real.log ((268 : ℕ)) / 2 := by
    have h := (log_br_268).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((268 : ℕ)) / 2 ≤ ((5590987/2000000 : ℚ) : ℝ) := by
    have h := (log_br_268).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3025913/10000000) (δ := 5633/500000000) (ψ := -125063/500000) 449 200
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t268 : ((53850438979/2500000000000 : ℚ) : ℝ) ≤ stT449o2 268 := by
  have hc : ((88157/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((268 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).1
  have hw2 : ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53850438979/2500000000000 : ℚ) : ℝ)
      = ((610847/10000000 : ℚ) : ℝ) * ((88157/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c269 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((269 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((930787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55947113/20000000 : ℚ) : ℝ) ≤ Real.log ((269 : ℕ)) / 2 := by
    have h := (log_br_269).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((269 : ℕ)) / 2 ≤ ((27973557/10000000 : ℚ) : ℝ) := by
    have h := (log_br_269).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -935593/10000000) (δ := 11387/1000000000) (ψ := -125063/500000) 449 200
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t269 : ((56747965627/1000000000000 : ℚ) : ℝ) ≤ stT449o2 269 := by
  have hc : ((930737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((269 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56747965627/1000000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((930737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c270 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((270 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((224147/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55984219/20000000 : ℚ) : ℝ) ≤ Real.log ((270 : ℕ)) / 2 := by
    have h := (log_br_270).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((270 : ℕ)) / 2 ≤ ((2799211/1000000 : ℚ) : ℝ) := by
    have h := (log_br_270).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1146981/10000000) (δ := 11287/1000000000) (ψ := -125063/500000) 449 200
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t270 : ((13640377401/250000000000 : ℚ) : ℝ) ≤ stT449o2 270 := by
  have hc : ((448269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((270 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13640377401/250000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((448269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c271 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((271 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((11133/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14005297/5000000 : ℚ) : ℝ) ≤ Real.log ((271 : ℕ)) / 2 := by
    have h := (log_br_271).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((271 : ℕ)) / 2 ≤ ((56021189/20000000 : ℚ) : ℝ) := by
    have h := (log_br_271).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1610933/5000000) (δ := 11237/1000000000) (ψ := -125063/500000) 449 200
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t271 : ((211299773/12500000000 : ℚ) : ℝ) ≤ stT449o2 271 := by
  have hc : ((11131/40000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((271 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211299773/12500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((11131/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c272 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((272 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-518271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2802901/1000000 : ℚ) : ℝ) ≤ Real.log ((272 : ℕ)) / 2 := by
    have h := (log_br_272).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((272 : ℕ)) / 2 ≤ ((56058021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_272).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2644531/5000000) (δ := 11237/1000000000) (ψ := -125063/500000) 449 200
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t272 : ((-15713937757/500000000000 : ℚ) : ℝ) ≤ stT449o2 272 := by
  have hc : ((-518321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((272 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15713937757/500000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-518321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c273 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((273 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-979643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56094717/20000000 : ℚ) : ℝ) ≤ Real.log ((273 : ℕ)) / 2 := by
    have h := (log_br_273).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((273 : ℕ)) / 2 ≤ ((28047359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_273).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7348681/10000000) (δ := 5633/500000000) (ψ := -125063/500000) 449 200
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t273 : ((-148234408751/2500000000000 : ℚ) : ℝ) ≤ stT449o2 273 := by
  have hc : ((-979693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((273 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148234408751/2500000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-979693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c274 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((274 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-814609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56131281/20000000 : ℚ) : ℝ) ≤ Real.log ((274 : ℕ)) / 2 := by
    have h := (log_br_274).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((274 : ℕ)) / 2 ≤ ((28065641/10000000 : ℚ) : ℝ) := by
    have h := (log_br_274).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -788391/1250000) (δ := 5679/500000000) (ψ := -125063/500000) 449 201
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t274 : ((-492154239057/10000000000000 : ℚ) : ℝ) ≤ stT449o2 274 := by
  have hc : ((-814659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((274 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-492154239057/10000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-814659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c275 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((275 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-133821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5616771/2000000 : ℚ) : ℝ) ≤ Real.log ((275 : ℕ)) / 2 := by
    have h := (log_br_275).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((275 : ℕ)) / 2 ≤ ((56167711/20000000 : ℚ) : ℝ) := by
    have h := (log_br_275).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -85251/200000) (δ := 2249/200000000) (ψ := -125063/500000) 449 201
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t275 : ((-80727292033/10000000000000 : ℚ) : ℝ) ≤ stT449o2 275 := by
  have hc : ((-133871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((275 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80727292033/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-133871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c276 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((276 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((629311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7025501/2500000 : ℚ) : ℝ) ≤ Real.log ((276 : ℕ)) / 2 := by
    have h := (log_br_276).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((276 : ℕ)) / 2 ≤ ((56204009/20000000 : ℚ) : ℝ) := by
    have h := (log_br_276).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -89013/400000) (δ := 2827/250000000) (ψ := -125063/500000) 449 201
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t276 : ((378770444469/10000000000000 : ℚ) : ℝ) ≤ stT449o2 276 := by
  have hc : ((629261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((276 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((378770444469/10000000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((629261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c277 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((277 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((199389/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2249607/800000 : ℚ) : ℝ) ≤ Real.log ((277 : ℕ)) / 2 := by
    have h := (log_br_277).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((277 : ℕ)) / 2 ≤ ((3515011/1250000 : ℚ) : ℝ) := by
    have h := (log_br_277).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -48863/2500000) (δ := 5629/500000000) (ψ := -125063/500000) 449 201
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t277 : ((119795077739/2000000000000 : ℚ) : ℝ) ≤ stT449o2 277 := by
  have hc : ((199379/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((277 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119795077739/2000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((199379/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c278 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((278 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((372311/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56276211/20000000 : ℚ) : ℝ) ≤ Real.log ((278 : ℕ)) / 2 := by
    have h := (log_br_278).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((278 : ℕ)) / 2 ≤ ((14069053/5000000 : ℚ) : ℝ) := by
    have h := (log_br_278).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1827069/10000000) (δ := 2279/200000000) (ψ := -125063/500000) 449 201
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t278 : ((1395514071/31250000000 : ℚ) : ℝ) ≤ stT449o2 278 := by
  have hc : ((186143/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((278 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1395514071/31250000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((186143/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c279 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((279 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((33873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56312117/20000000 : ℚ) : ℝ) ≤ Real.log ((279 : ℕ)) / 2 := by
    have h := (log_br_279).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((279 : ℕ)) / 2 ≤ ((28156059/10000000 : ℚ) : ℝ) := by
    have h := (log_br_279).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3842293/10000000) (δ := 2259/200000000) (ψ := -125063/500000) 449 201
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t279 : ((5062322233/2500000000000 : ℚ) : ℝ) ≤ stT449o2 279 := by
  have hc : ((33823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((279 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5062322233/2500000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((33823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c280 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((280 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-27827/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7043487/2500000 : ℚ) : ℝ) ≤ Real.log ((280 : ℕ)) / 2 := by
    have h := (log_br_280).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((280 : ℕ)) / 2 ≤ ((56347897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_280).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5850389/10000000) (δ := 2827/250000000) (ψ := -125063/500000) 449 201
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t280 : ((-3326205567/80000000000 : ℚ) : ℝ) ≤ stT449o2 280 := by
  have hc : ((-27829/40000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((280 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3326205567/80000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-27829/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c281 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((281 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28191773/10000000 : ℚ) : ℝ) ≤ Real.log ((281 : ℕ)) / 2 := by
    have h := (log_br_281).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((281 : ℕ)) / 2 ≤ ((56383547/20000000 : ℚ) : ℝ) := by
    have h := (log_br_281).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1570249/2000000) (δ := 713/62500000) (ψ := -125063/500000) 449 201
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t281 : ((-11931584619/200000000000 : ℚ) : ℝ) ≤ stT449o2 281 := by
  have hc : ((-1000049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((281 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11931584619/200000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-1000049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c282 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((282 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-699271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5641907/2000000 : ℚ) : ℝ) ≤ Real.log ((282 : ℕ)) / 2 := by
    have h := (log_br_282).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((282 : ℕ)) / 2 ≤ ((56419071/20000000 : ℚ) : ℝ) := by
    have h := (log_br_282).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5862933/10000000) (δ := 1419/125000000) (ψ := -125063/500000) 449 202
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t282 : ((-104110015233/2500000000000 : ℚ) : ℝ) ≤ stT449o2 282 := by
  have hc : ((-699321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((282 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).2
  have h0 : (0:ℝ) ≤ ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104110015233/2500000000000 : ℚ) : ℝ)
      = ((148873/2500000 : ℚ) : ℝ) * ((-699321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c283 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((283 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((20307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14113617/5000000 : ℚ) : ℝ) ≤ Real.log ((283 : ℕ)) / 2 := by
    have h := (log_br_283).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((283 : ℕ)) / 2 ≤ ((56454469/20000000 : ℚ) : ℝ) := by
    have h := (log_br_283).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3876221/10000000) (δ := 11401/1000000000) (ψ := -125063/500000) 449 202
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t283 : ((6020765283/5000000000000 : ℚ) : ℝ) ≤ stT449o2 283 := by
  have hc : ((20257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((283 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6020765283/5000000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((20257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c284 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((284 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((725809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28244871/10000000 : ℚ) : ℝ) ≤ Real.log ((284 : ℕ)) / 2 := by
    have h := (log_br_284).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((284 : ℕ)) / 2 ≤ ((56489743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_284).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1896467/10000000) (δ := 1419/125000000) (ψ := -125063/500000) 449 202
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t284 : ((43065813301/1000000000000 : ℚ) : ℝ) ≤ stT449o2 284 := by
  have hc : ((725759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((284 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43065813301/1000000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((725759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c285 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((285 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((199907/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56524891/20000000 : ℚ) : ℝ) ≤ Real.log ((285 : ℕ)) / 2 := by
    have h := (log_br_285).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((285 : ℕ)) / 2 ≤ ((14131223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_285).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7627/1000000) (δ := 11351/1000000000) (ψ := -125063/500000) 449 202
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t285 : ((29602147039/500000000000 : ℚ) : ℝ) ≤ stT449o2 285 := by
  have hc : ((199897/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((285 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29602147039/500000000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((199897/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c286 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((286 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((68451/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28279959/10000000 : ℚ) : ℝ) ≤ Real.log ((286 : ℕ)) / 2 := by
    have h := (log_br_286).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((286 : ℕ)) / 2 ≤ ((56559919/20000000 : ℚ) : ℝ) := by
    have h := (log_br_286).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2042161/10000000) (δ := 1419/125000000) (ψ := -125063/500000) 449 202
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t286 : ((1264779411/31250000000 : ℚ) : ℝ) ≤ stT449o2 286 := by
  have hc : ((34223/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((286 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).1
  have hw2 : ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((36957/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1264779411/31250000000 : ℚ) : ℝ)
      = ((36957/625000 : ℚ) : ℝ) * ((34223/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c287 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((287 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-29659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28297411/10000000 : ℚ) : ℝ) ≤ Real.log ((287 : ℕ)) / 2 := by
    have h := (log_br_287).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((287 : ℕ)) / 2 ≤ ((56594823/20000000 : ℚ) : ℝ) := by
    have h := (log_br_287).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1000287/2500000) (δ := 1419/125000000) (ψ := -125063/500000) 449 202
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t287 : ((-8768343969/5000000000000 : ℚ) : ℝ) ≤ stT449o2 287 := by
  have hc : ((-29709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((287 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8768343969/5000000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-29709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c288 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((288 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-144929/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14157401/5000000 : ℚ) : ℝ) ≤ Real.log ((288 : ℕ)) / 2 := by
    have h := (log_br_288).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((288 : ℕ)) / 2 ≤ ((11325921/4000000 : ℚ) : ℝ) := by
    have h := (log_br_288).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5953287/10000000) (δ := 11401/1000000000) (ψ := -125063/500000) 449 202
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t288 : ((-10675771923/250000000000 : ℚ) : ℝ) ≤ stT449o2 288 := by
  have hc : ((-144939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((288 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).2
  have h0 : (0:ℝ) ≤ ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10675771923/250000000000 : ℚ) : ℝ)
      = ((73657/1250000 : ℚ) : ℝ) * ((-144939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c289 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((289 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-6249/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28332133/10000000 : ℚ) : ℝ) ≤ Real.log ((289 : ℕ)) / 2 := by
    have h := (log_br_289).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((289 : ℕ)) / 2 ≤ ((56664267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_289).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7809271/10000000) (δ := 11259/1000000000) (ψ := -125063/500000) 449 203
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t289 : ((-14704282351/250000000000 : ℚ) : ℝ) ≤ stT449o2 289 := by
  have hc : ((-99989/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((289 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).2
  have h0 : (0:ℝ) ≤ ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14704282351/250000000000 : ℚ) : ℝ)
      = ((147059/2500000 : ℚ) : ℝ) * ((-99989/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c290 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((290 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-175361/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56698809/20000000 : ℚ) : ℝ) ≤ Real.log ((290 : ℕ)) / 2 := by
    have h := (log_br_290).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((290 : ℕ)) / 2 ≤ ((5669881/2000000 : ℚ) : ℝ) := by
    have h := (log_br_290).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1174109/2000000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 203
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t290 : ((-205966004087/5000000000000 : ℚ) : ℝ) ≤ stT449o2 290 := by
  have hc : ((-350747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((290 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205966004087/5000000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-350747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c291 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((291 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-37/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3545827/1250000 : ℚ) : ℝ) ≤ Real.log ((291 : ℕ)) / 2 := by
    have h := (log_br_291).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((291 : ℕ)) / 2 ≤ ((56733233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_291).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1969277/5000000) (δ := 11359/1000000000) (ψ := -125063/500000) 449 203
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t291 : ((-109621457/400000000000 : ℚ) : ℝ) ≤ stT449o2 291 := by
  have hc : ((-187/40000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((291 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).2
  have h0 : (0:ℝ) ≤ ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109621457/400000000000 : ℚ) : ℝ)
      = ((586211/10000000 : ℚ) : ℝ) * ((-187/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c292 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((292 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((69293/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28383769/10000000 : ℚ) : ℝ) ≤ Real.log ((292 : ℕ)) / 2 := by
    have h := (log_br_292).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((292 : ℕ)) / 2 ≤ ((56767539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_292).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -201313/1000000) (δ := 11259/1000000000) (ψ := -125063/500000) 449 203
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t292 : ((1013692101/25000000000 : ℚ) : ℝ) ≤ stT449o2 292 := by
  have hc : ((8661/12500 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((292 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1013692101/25000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((8661/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c293 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((293 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((124911/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28400863/10000000 : ℚ) : ℝ) ≤ Real.log ((293 : ℕ)) / 2 := by
    have h := (log_br_293).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((293 : ℕ)) / 2 ≤ ((56801727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_293).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -94329/10000000) (δ := 5697/500000000) (ψ := -125063/500000) 449 203
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t293 : ((145940208757/2500000000000 : ℚ) : ℝ) ≤ stT449o2 293 := by
  have hc : ((499619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((293 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145940208757/2500000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((499619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c294 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((294 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((93383/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56835797/20000000 : ℚ) : ℝ) ≤ Real.log ((294 : ℕ)) / 2 := by
    have h := (log_br_294).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((294 : ℕ)) / 2 ≤ ((28417899/10000000 : ℚ) : ℝ) := by
    have h := (log_br_294).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 908953/5000000) (δ := 709/62500000) (ψ := -125063/500000) 449 203
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t294 : ((217833390977/5000000000000 : ℚ) : ℝ) ≤ stT449o2 294 := by
  have hc : ((373507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((294 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).1
  have hw2 : ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((583211/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217833390977/5000000000000 : ℚ) : ℝ)
      = ((583211/10000000 : ℚ) : ℝ) * ((373507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c295 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((295 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((5077/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56869753/20000000 : ℚ) : ℝ) ≤ Real.log ((295 : ℕ)) / 2 := by
    have h := (log_br_295).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((295 : ℕ)) / 2 ≤ ((28434877/10000000 : ℚ) : ℝ) := by
    have h := (log_br_295).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3723687/10000000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 203
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t295 : ((11816486601/2500000000000 : ℚ) : ℝ) ≤ stT449o2 295 := by
  have hc : ((40591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((295 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11816486601/2500000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((40591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c296 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((296 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-125511/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28451797/10000000 : ℚ) : ℝ) ≤ Real.log ((296 : ℕ)) / 2 := by
    have h := (log_br_296).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((296 : ℕ)) / 2 ≤ ((11380719/4000000 : ℚ) : ℝ) := by
    have h := (log_br_296).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5623013/10000000) (δ := 11259/1000000000) (ψ := -125063/500000) 449 203
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t296 : ((-72957700519/2000000000000 : ℚ) : ℝ) ≤ stT449o2 296 := by
  have hc : ((-125521/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((296 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72957700519/2000000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-125521/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c297 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((297 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-123859/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56937321/20000000 : ℚ) : ℝ) ≤ Real.log ((297 : ℕ)) / 2 := by
    have h := (log_br_297).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((297 : ℕ)) / 2 ≤ ((28468661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_297).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7515941/10000000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 203
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t297 : ((-287495704399/5000000000000 : ℚ) : ℝ) ≤ stT449o2 297 := by
  have hc : ((-495461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((297 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-287495704399/5000000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-495461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c298 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((298 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-81423/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28485467/10000000 : ℚ) : ℝ) ≤ Real.log ((298 : ℕ)) / 2 := by
    have h := (log_br_298).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((298 : ℕ)) / 2 ≤ ((11394187/4000000 : ℚ) : ℝ) := by
    have h := (log_br_298).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6305493/10000000) (δ := 11287/1000000000) (ψ := -125063/500000) 449 204
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t298 : ((-2358500949/50000000000 : ℚ) : ℝ) ≤ stT449o2 298 := by
  have hc : ((-20357/25000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((298 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2358500949/50000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-20357/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c299 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((299 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-98993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11400887/4000000 : ℚ) : ℝ) ≤ Real.log ((299 : ℕ)) / 2 := by
    have h := (log_br_299).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((299 : ℕ)) / 2 ≤ ((14251109/5000000 : ℚ) : ℝ) := by
    have h := (log_br_299).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4425249/10000000) (δ := 2829/250000000) (ψ := -125063/500000) 449 204
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t299 : ((-5726359467/500000000000 : ℚ) : ℝ) ≤ stT449o2 299 := by
  have hc : ((-49509/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((299 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5726359467/500000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-49509/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c300 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((300 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((261463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((222804/78125 : ℚ) : ℝ) ≤ Real.log ((300 : ℕ)) / 2 := by
    have h := (log_br_300).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((300 : ℕ)) / 2 ≤ ((2281513/800000 : ℚ) : ℝ) := by
    have h := (log_br_300).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -637823/2500000) (δ := 11387/1000000000) (ψ := -125063/500000) 449 204
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t300 : ((1509412293/50000000000 : ℚ) : ℝ) ≤ stT449o2 300 := by
  have hc : ((130719/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((300 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1509412293/50000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((130719/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c301 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((301 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((240713/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28535551/10000000 : ℚ) : ℝ) ≤ Real.log ((301 : ℕ)) / 2 := by
    have h := (log_br_301).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((301 : ℕ)) / 2 ≤ ((57071103/20000000 : ℚ) : ℝ) := by
    have h := (log_br_301).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -170891/2500000) (δ := 11287/1000000000) (ψ := -125063/500000) 449 204
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t301 : ((27747472239/500000000000 : ℚ) : ℝ) ≤ stT449o2 301 := by
  have hc : ((481401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((301 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27747472239/500000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((481401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c302 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((302 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((445513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5710427/2000000 : ℚ) : ℝ) ≤ Real.log ((302 : ℕ)) / 2 := by
    have h := (log_br_302).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((302 : ℕ)) / 2 ≤ ((57104271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_302).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 117799/1000000) (δ := 11287/1000000000) (ψ := -125063/500000) 449 204
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t302 : ((3204367341/62500000000 : ℚ) : ℝ) ≤ stT449o2 302 := by
  have hc : ((27843/31250 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((302 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3204367341/62500000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((27843/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c303 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((303 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((69977/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3571083/1250000 : ℚ) : ℝ) ≤ Real.log ((303 : ℕ)) / 2 := by
    have h := (log_br_303).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((303 : ℕ)) / 2 ≤ ((57137329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_303).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 303337/1000000) (δ := 11387/1000000000) (ψ := -125063/500000) 449 204
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t303 : ((10048730507/500000000000 : ℚ) : ℝ) ≤ stT449o2 303 := by
  have hc : ((69967/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((303 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10048730507/500000000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((69967/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c304 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((304 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-74603/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57170277/20000000 : ℚ) : ℝ) ≤ Real.log ((304 : ℕ)) / 2 := by
    have h := (log_br_304).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((304 : ℕ)) / 2 ≤ ((28585139/10000000 : ℚ) : ℝ) := by
    have h := (log_br_304).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4882633/10000000) (δ := 11237/1000000000) (ψ := -125063/500000) 449 204
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t304 : ((-2139677001/100000000000 : ℚ) : ℝ) ≤ stT449o2 304 := by
  have hc : ((-74613/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((304 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2139677001/100000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-74613/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c305 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((305 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-899889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57203117/20000000 : ℚ) : ℝ) ≤ Real.log ((305 : ℕ)) / 2 := by
    have h := (log_br_305).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((305 : ℕ)) / 2 ≤ ((28601559/10000000 : ℚ) : ℝ) := by
    have h := (log_br_305).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3362889/5000000) (δ := 11237/1000000000) (ψ := -125063/500000) 449 204
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t305 : ((-515304171461/10000000000000 : ℚ) : ℝ) ≤ stT449o2 305 := by
  have hc : ((-899939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((305 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-515304171461/10000000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-899939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c306 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((306 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-192011/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57235851/20000000 : ℚ) : ℝ) ≤ Real.log ((306 : ℕ)) / 2 := by
    have h := (log_br_306).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((306 : ℕ)) / 2 ≤ ((14308963/5000000 : ℚ) : ℝ) := by
    have h := (log_br_306).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7144989/10000000) (δ := 11423/1000000000) (ψ := -125063/500000) 449 205
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t306 : ((-54885554451/1000000000000 : ℚ) : ℝ) ≤ stT449o2 306 := by
  have hc : ((-192021/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((306 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54885554451/1000000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-192021/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c307 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((307 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-526727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57268477/20000000 : ℚ) : ℝ) ≤ Real.log ((307 : ℕ)) / 2 := by
    have h := (log_br_307).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((307 : ℕ)) / 2 ≤ ((28634239/10000000 : ℚ) : ℝ) := by
    have h := (log_br_307).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1062771/2000000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 205
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t307 : ((-300647963987/10000000000000 : ℚ) : ℝ) ≤ stT449o2 307 := by
  have hc : ((-526777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((307 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).2
  have h0 : (0:ℝ) ≤ ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-300647963987/10000000000000 : ℚ) : ℝ)
      = ((570731/10000000 : ℚ) : ℝ) * ((-526777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c308 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((308 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((174431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57300997/20000000 : ℚ) : ℝ) ≤ Real.log ((308 : ℕ)) / 2 := by
    have h := (log_br_308).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((308 : ℕ)) / 2 ≤ ((28650499/10000000 : ℚ) : ℝ) := by
    have h := (log_br_308).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -348867/1000000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 205
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t308 : ((49681321281/5000000000000 : ℚ) : ℝ) ≤ stT449o2 308 := by
  have hc : ((174381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((308 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49681321281/5000000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((174381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c309 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((309 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((12269/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14333353/5000000 : ℚ) : ℝ) ≤ Real.log ((309 : ℕ)) / 2 := by
    have h := (log_br_309).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((309 : ℕ)) / 2 ≤ ((57333413/20000000 : ℚ) : ℝ) := by
    have h := (log_br_309).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -834689/5000000) (δ := 11373/1000000000) (ψ := -125063/500000) 449 205
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t309 : ((2791657713/62500000000 : ℚ) : ℝ) ≤ stT449o2 309 := by
  have hc : ((392583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((309 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2791657713/62500000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((392583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c310 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((310 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((998341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28682861/10000000 : ℚ) : ℝ) ≤ Real.log ((310 : ℕ)) / 2 := by
    have h := (log_br_310).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((310 : ℕ)) / 2 ≤ ((57365723/20000000 : ℚ) : ℝ) := by
    have h := (log_br_310).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7201/500000) (δ := 569/50000000) (ψ := -125063/500000) 449 205
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t310 : ((566990354651/10000000000000 : ℚ) : ℝ) ≤ stT449o2 310 := by
  have hc : ((998291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((310 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).1
  have hw2 : ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567961/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((566990354651/10000000000000 : ℚ) : ℝ)
      = ((567961/10000000 : ℚ) : ℝ) * ((998291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c311 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((311 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((710453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57397929/20000000 : ℚ) : ℝ) ≤ Real.log ((311 : ℕ)) / 2 := by
    have h := (log_br_311).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((311 : ℕ)) / 2 ≤ ((5739793/2000000 : ℚ) : ℝ) := by
    have h := (log_br_311).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 975819/5000000) (δ := 1133/100000000) (ψ := -125063/500000) 449 205
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t311 : ((402831889941/10000000000000 : ℚ) : ℝ) ≤ stT449o2 311 := by
  have hc : ((710403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((311 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((402831889941/10000000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((710403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c312 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((312 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((13879/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57430031/20000000 : ℚ) : ℝ) ≤ Real.log ((312 : ℕ)) / 2 := by
    have h := (log_br_312).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((312 : ℕ)) / 2 ≤ ((3589377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_312).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3753363/10000000) (δ := 1123/100000000) (ψ := -125063/500000) 449 205
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t312 : ((3925883961/1000000000000 : ℚ) : ℝ) ≤ stT449o2 312 := by
  have hc : ((13869/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((312 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).1
  have hw2 : ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((283069/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3925883961/1000000000000 : ℚ) : ℝ)
      = ((283069/5000000 : ℚ) : ℝ) * ((13869/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c313 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((313 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-604349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57462031/20000000 : ℚ) : ℝ) ≤ Real.log ((313 : ℕ)) / 2 := by
    have h := (log_br_313).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((313 : ℕ)) / 2 ≤ ((3591377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_313).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5549363/10000000) (δ := 1123/100000000) (ψ := -125063/500000) 449 205
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t313 : ((-170813432183/5000000000000 : ℚ) : ℝ) ≤ stT449o2 313 := by
  have hc : ((-604399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((313 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170813432183/5000000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-604399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c314 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((314 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-978911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57493929/20000000 : ℚ) : ℝ) ≤ Real.log ((314 : ℕ)) / 2 := by
    have h := (log_br_314).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((314 : ℕ)) / 2 ≤ ((5749393/2000000 : ℚ) : ℝ) := by
    have h := (log_br_314).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3669819/5000000) (δ := 1133/100000000) (ψ := -125063/500000) 449 205
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t314 : ((-552459998013/10000000000000 : ℚ) : ℝ) ≤ stT449o2 314 := by
  have hc : ((-978961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((314 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-552459998013/10000000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-978961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c315 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((315 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-218417/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28762863/10000000 : ℚ) : ℝ) ≤ Real.log ((315 : ℕ)) / 2 := by
    have h := (log_br_315).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((315 : ℕ)) / 2 ≤ ((57525727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_315).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3291859/5000000) (δ := 569/50000000) (ψ := -125063/500000) 449 206
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t315 : ((-246142524383/5000000000000 : ℚ) : ℝ) ≤ stT449o2 315 := by
  have hc : ((-436859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((315 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).2
  have h0 : (0:ℝ) ≤ ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246142524383/5000000000000 : ℚ) : ℝ)
      = ((563437/10000000 : ℚ) : ℝ) * ((-436859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c316 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((316 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-171973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28778711/10000000 : ℚ) : ℝ) ≤ Real.log ((316 : ℕ)) / 2 := by
    have h := (log_br_316).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((316 : ℕ)) / 2 ≤ ((57557423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_316).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -240239/500000) (δ := 569/50000000) (ψ := -125063/500000) 449 206
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t316 : ((-3023638841/156250000000 : ℚ) : ℝ) ≤ stT449o2 316 := by
  have hc : ((-85999/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((316 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3023638841/156250000000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-85999/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c317 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((317 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((350581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57589017/20000000 : ℚ) : ℝ) ≤ Real.log ((317 : ℕ)) / 2 := by
    have h := (log_br_317).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((317 : ℕ)) / 2 ≤ ((28794509/10000000 : ℚ) : ℝ) := by
    have h := (log_br_317).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3031511/10000000) (δ := 1123/100000000) (ψ := -125063/500000) 449 206
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t317 : ((39375497761/2000000000000 : ℚ) : ℝ) ≤ stT449o2 317 := by
  have hc : ((350531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((317 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39375497761/2000000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((350531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c318 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((318 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((874923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57620513/20000000 : ℚ) : ℝ) ≤ Real.log ((318 : ℕ)) / 2 := by
    have h := (log_br_318).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((318 : ℕ)) / 2 ≤ ((28810257/10000000 : ℚ) : ℝ) := by
    have h := (log_br_318).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -631899/5000000) (δ := 1123/100000000) (ψ := -125063/500000) 449 206
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t318 : ((122651070489/2500000000000 : ℚ) : ℝ) ≤ stT449o2 318 := by
  have hc : ((874873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((318 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122651070489/2500000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((874873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c319 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((319 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((30631/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57651911/20000000 : ℚ) : ℝ) ≤ Real.log ((319 : ℕ)) / 2 := by
    have h := (log_br_319).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((319 : ℕ)) / 2 ≤ ((7206489/2500000 : ℚ) : ℝ) := by
    have h := (log_br_319).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 99683/2000000) (δ := 1133/100000000) (ψ := -125063/500000) 449 206
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t319 : ((68596708083/1250000000000 : ℚ) : ℝ) ≤ stT449o2 319 := by
  have hc : ((490071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((319 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).1
  have hw2 : ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((139973/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68596708083/1250000000000 : ℚ) : ℝ)
      = ((139973/2500000 : ℚ) : ℝ) * ((490071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c320 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((320 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((620037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57683209/20000000 : ℚ) : ℝ) ≤ Real.log ((320 : ℕ)) / 2 := by
    have h := (log_br_320).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((320 : ℕ)) / 2 ≤ ((5768321/2000000 : ℚ) : ℝ) := by
    have h := (log_br_320).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 451003/2000000) (δ := 1123/100000000) (ψ := -125063/500000) 449 206
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t320 : ((43322831599/1250000000000 : ℚ) : ℝ) ≤ stT449o2 320 := by
  have hc : ((619987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((320 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43322831599/1250000000000 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((619987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c321 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((321 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-31689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57714411/20000000 : ℚ) : ℝ) ≤ Real.log ((321 : ℕ)) / 2 := by
    have h := (log_br_321).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((321 : ℕ)) / 2 ≤ ((14428603/5000000 : ℚ) : ℝ) := by
    have h := (log_br_321).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4006227/10000000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 206
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t321 : ((-8857497947/5000000000000 : ℚ) : ℝ) ≤ stT449o2 321 := by
  have hc : ((-31739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((321 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8857497947/5000000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-31739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c322 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((322 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-333427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11549103/4000000 : ℚ) : ℝ) ≤ Real.log ((322 : ℕ)) / 2 := by
    have h := (log_br_322).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((322 : ℕ)) / 2 ≤ ((14436379/5000000 : ℚ) : ℝ) := by
    have h := (log_br_322).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5751939/10000000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 206
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t322 : ((-46456449277/1250000000000 : ℚ) : ℝ) ≤ stT449o2 322 := by
  have hc : ((-83363/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((322 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46456449277/1250000000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-83363/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c323 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((323 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-989551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57776523/20000000 : ℚ) : ℝ) ≤ Real.log ((323 : ℕ)) / 2 := by
    have h := (log_br_323).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((323 : ℕ)) / 2 ≤ ((14444131/5000000 : ℚ) : ℝ) := by
    have h := (log_br_323).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7492263/10000000) (δ := 11323/1000000000) (ψ := -125063/500000) 449 206
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t323 : ((-110125768083/2000000000000 : ℚ) : ℝ) ≤ stT449o2 323 := by
  have hc : ((-989601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((323 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110125768083/2000000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-989601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c324 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((324 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-852897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11561487/4000000 : ℚ) : ℝ) ≤ Real.log ((324 : ℕ)) / 2 := by
    have h := (log_br_324).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((324 : ℕ)) / 2 ≤ ((14451859/5000000 : ℚ) : ℝ) := by
    have h := (log_br_324).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1620191/2500000) (δ := 5619/500000000) (ψ := -125063/500000) 449 207
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t324 : ((-118464955883/2500000000000 : ℚ) : ℝ) ≤ stT449o2 324 := by
  have hc : ((-852947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((324 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118464955883/2500000000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-852947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c325 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((325 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-259/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57838251/20000000 : ℚ) : ℝ) ≤ Real.log ((325 : ℕ)) / 2 := by
    have h := (log_br_325).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((325 : ℕ)) / 2 ≤ ((14459563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_325).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -296951/625000) (δ := 5619/500000000) (ψ := -125063/500000) 449 207
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t325 : ((-898060919/50000000000 : ℚ) : ℝ) ≤ stT449o2 325 := by
  have hc : ((-1619/5000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((325 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-898060919/50000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-1619/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c326 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((326 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((88073/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57868973/20000000 : ℚ) : ℝ) ≤ Real.log ((326 : ℕ)) / 2 := by
    have h := (log_br_326).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((326 : ℕ)) / 2 ≤ ((28934487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_326).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -23648/78125) (δ := 2263/200000000) (ψ := -125063/500000) 449 207
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t326 : ((12193032951/625000000000 : ℚ) : ℝ) ≤ stT449o2 326 := by
  have hc : ((176121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((326 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12193032951/625000000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((176121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c327 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((327 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((173247/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57899601/20000000 : ℚ) : ℝ) ≤ Real.log ((327 : ℕ)) / 2 := by
    have h := (log_br_327).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((327 : ℕ)) / 2 ≤ ((28949801/10000000 : ℚ) : ℝ) := by
    have h := (log_br_327).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1307947/10000000) (δ := 5669/500000000) (ψ := -125063/500000) 449 207
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t327 : ((95800234237/2000000000000 : ℚ) : ℝ) ≤ stT449o2 327 := by
  have hc : ((173237/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((327 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95800234237/2000000000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((173237/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c328 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((328 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((986853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7241267/2500000 : ℚ) : ℝ) ≤ Real.log ((328 : ℕ)) / 2 := by
    have h := (log_br_328).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((328 : ℕ)) / 2 ≤ ((57930137/20000000 : ℚ) : ℝ) := by
    have h := (log_br_328).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 40583/1000000) (δ := 2847/250000000) (ψ := -125063/500000) 449 207
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t328 : ((544870184071/10000000000000 : ℚ) : ℝ) ≤ stT449o2 328 := by
  have hc : ((986803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((328 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((544870184071/10000000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((986803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c329 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((329 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((663183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57960577/20000000 : ℚ) : ℝ) ≤ Real.log ((329 : ℕ)) / 2 := by
    have h := (log_br_329).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((329 : ℕ)) / 2 ≤ ((28980289/10000000 : ℚ) : ℝ) := by
    have h := (log_br_329).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2114331/10000000) (δ := 5669/500000000) (ψ := -125063/500000) 449 207
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t329 : ((365596496161/10000000000000 : ℚ) : ℝ) ≤ stT449o2 329 := by
  have hc : ((663133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((329 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365596496161/10000000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((663133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c330 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((330 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((8743/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28995463/10000000 : ℚ) : ℝ) ≤ Real.log ((330 : ℕ)) / 2 := by
    have h := (log_br_330).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((330 : ℕ)) / 2 ≤ ((57990927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_330).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 954417/2500000) (δ := 2273/200000000) (ψ := -125063/500000) 449 207
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t330 : ((4807350573/2000000000000 : ℚ) : ℝ) ≤ stT449o2 330 := by
  have hc : ((8733/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((330 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4807350573/2000000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((8733/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c331 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((331 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-593613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58021183/20000000 : ℚ) : ℝ) ≤ Real.log ((331 : ℕ)) / 2 := by
    have h := (log_br_331).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((331 : ℕ)) / 2 ≤ ((906581/312500 : ℚ) : ℝ) := by
    have h := (log_br_331).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2757921/5000000) (δ := 2283/200000000) (ψ := -125063/500000) 449 207
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t331 : ((-6526137359/200000000000 : ℚ) : ℝ) ≤ stT449o2 331 := by
  have hc : ((-593663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((331 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6526137359/200000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-593663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c332 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((332 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-193379/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58051349/20000000 : ℚ) : ℝ) ≤ Real.log ((332 : ℕ)) / 2 := by
    have h := (log_br_332).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((332 : ℕ)) / 2 ≤ ((1161027/400000 : ℚ) : ℝ) := by
    have h := (log_br_332).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7208909/10000000) (δ := 2263/200000000) (ψ := -125063/500000) 449 207
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t332 : ((-53068068879/1000000000000 : ℚ) : ℝ) ≤ stT449o2 332 := by
  have hc : ((-193389/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((332 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53068068879/1000000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-193389/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c333 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((333 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-182849/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3630089/1250000 : ℚ) : ℝ) ≤ Real.log ((333 : ℕ)) / 2 := by
    have h := (log_br_333).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((333 : ℕ)) / 2 ≤ ((2323257/800000 : ℚ) : ℝ) := by
    have h := (log_br_333).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1362219/2000000) (δ := 5679/500000000) (ψ := -125063/500000) 449 208
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t333 : ((-100206183423/2000000000000 : ℚ) : ℝ) ≤ stT449o2 333 := by
  have hc : ((-182859/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((333 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).2
  have h0 : (0:ℝ) ≤ ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100206183423/2000000000000 : ℚ) : ℝ)
      = ((547997/10000000 : ℚ) : ℝ) * ((-182859/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c334 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((334 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-115551/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58111409/20000000 : ℚ) : ℝ) ≤ Real.log ((334 : ℕ)) / 2 := by
    have h := (log_br_334).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((334 : ℕ)) / 2 ≤ ((5811141/2000000 : ℚ) : ℝ) := by
    have h := (log_br_334).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5128187/10000000) (δ := 713/62500000) (ψ := -125063/500000) 449 208
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t334 : ((-15808393419/625000000000 : ℚ) : ℝ) ≤ stT449o2 334 := by
  have hc : ((-231127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((334 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15808393419/625000000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-231127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c335 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((335 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((189533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11628261/4000000 : ℚ) : ℝ) ≤ Real.log ((335 : ℕ)) / 2 := by
    have h := (log_br_335).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((335 : ℕ)) / 2 ≤ ((29070653/10000000 : ℚ) : ℝ) := by
    have h := (log_br_335).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1725137/5000000) (δ := 713/62500000) (ψ := -125063/500000) 449 208
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t335 : ((51762776457/5000000000000 : ℚ) : ℝ) ≤ stT449o2 335 := by
  have hc : ((189483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((335 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51762776457/5000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((189483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c336 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((336 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((757733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58171111/20000000 : ℚ) : ℝ) ≤ Real.log ((336 : ℕ)) / 2 := by
    have h := (log_br_336).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((336 : ℕ)) / 2 ≤ ((7271389/2500000 : ℚ) : ℝ) := by
    have h := (log_br_336).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -444353/2500000) (δ := 2827/250000000) (ψ := -125063/500000) 449 208
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t336 : ((51668676819/1250000000000 : ℚ) : ℝ) ≤ stT449o2 336 := by
  have hc : ((757683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((336 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51668676819/1250000000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((757683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c337 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((337 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((999041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58200829/20000000 : ℚ) : ℝ) ≤ Real.log ((337 : ℕ)) / 2 := by
    have h := (log_br_337).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((337 : ℕ)) / 2 ≤ ((5820083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_337).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -109489/10000000) (δ := 2249/200000000) (ψ := -125063/500000) 449 208
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t337 : ((272092181697/5000000000000 : ℚ) : ℝ) ≤ stT449o2 337 := by
  have hc : ((998991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((337 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272092181697/5000000000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((998991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c338 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((338 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((406539/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29115229/10000000 : ℚ) : ℝ) ≤ Real.log ((338 : ℕ)) / 2 := by
    have h := (log_br_338).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((338 : ℕ)) / 2 ≤ ((58230459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_338).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1553439/10000000) (δ := 2279/200000000) (ψ := -125063/500000) 449 208
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t338 : ((13819646687/312500000000 : ℚ) : ℝ) ≤ stT449o2 338 := by
  have hc : ((203257/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((338 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13819646687/312500000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((203257/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c339 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((339 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((28229/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58260001/20000000 : ℚ) : ℝ) ≤ Real.log ((339 : ℕ)) / 2 := by
    have h := (log_br_339).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((339 : ℕ)) / 2 ≤ ((29130001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_339).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3211539/10000000) (δ := 713/62500000) (ψ := -125063/500000) 449 208
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t339 : ((383229/25000000 : ℚ) : ℝ) ≤ stT449o2 339 := by
  have hc : ((882/3125 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((339 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((383229/25000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((882/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c340 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((340 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-366351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3643091/1250000 : ℚ) : ℝ) ≤ Real.log ((340 : ℕ)) / 2 := by
    have h := (log_br_340).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((340 : ℕ)) / 2 ≤ ((58289457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_340).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4864701/10000000) (δ := 5679/500000000) (ψ := -125063/500000) 449 208
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t340 : ((-198709155127/10000000000000 : ℚ) : ℝ) ≤ stT449o2 340 := by
  have hc : ((-366401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((340 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198709155127/10000000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-366401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c341 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((341 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-429777/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7289853/2500000 : ℚ) : ℝ) ≤ Real.log ((341 : ℕ)) / 2 := by
    have h := (log_br_341).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((341 : ℕ)) / 2 ≤ ((2332753/800000 : ℚ) : ℝ) := by
    have h := (log_br_341).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 325649/500000) (δ := 5679/500000000) (ψ := -125063/500000) 449 208
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t341 : ((-116375553431/2500000000000 : ℚ) : ℝ) ≤ stT449o2 341 := by
  have hc : ((-214901/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((341 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116375553431/2500000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-214901/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c342 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((342 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-62043/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58348107/20000000 : ℚ) : ℝ) ≤ Real.log ((342 : ℕ)) / 2 := by
    have h := (log_br_342).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((342 : ℕ)) / 2 ≤ ((14587027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_342).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -302059/400000) (δ := 11401/1000000000) (ψ := -125063/500000) 449 209
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t342 : ((-268406076691/5000000000000 : ℚ) : ℝ) ≤ stT449o2 342 := by
  have hc : ((-496369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((342 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268406076691/5000000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-496369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c343 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((343 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-178347/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7297163/2500000 : ℚ) : ℝ) ≤ Real.log ((343 : ℕ)) / 2 := by
    have h := (log_br_343).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((343 : ℕ)) / 2 ≤ ((11675461/4000000 : ℚ) : ℝ) := by
    have h := (log_br_343).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5912793/10000000) (δ := 11251/1000000000) (ψ := -125063/500000) 449 209
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t343 : ((-3852208481/100000000000 : ℚ) : ℝ) ≤ stT449o2 343 := by
  have hc : ((-356719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((343 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3852208481/100000000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-356719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c344 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((344 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-35073/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3650401/1250000 : ℚ) : ℝ) ≤ Real.log ((344 : ℕ)) / 2 := by
    have h := (log_br_344).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((344 : ℕ)) / 2 ≤ ((58406417/20000000 : ℚ) : ℝ) := by
    have h := (log_br_344).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2139441/5000000) (δ := 11251/1000000000) (ψ := -125063/500000) 449 209
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t344 : ((-9458419261/1250000000000 : ℚ) : ℝ) ≤ stT449o2 344 := by
  have hc : ((-70171/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((344 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9458419261/1250000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-70171/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c345 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((345 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((244491/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14608861/5000000 : ℚ) : ℝ) ≤ Real.log ((345 : ℕ)) / 2 := by
    have h := (log_br_345).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((345 : ℕ)) / 2 ≤ ((11687089/4000000 : ℚ) : ℝ) := by
    have h := (log_br_345).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -529937/2000000) (δ := 5701/500000000) (ψ := -125063/500000) 449 209
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t345 : ((65807924773/2500000000000 : ℚ) : ℝ) ≤ stT449o2 345 := by
  have hc : ((122233/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((345 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65807924773/2500000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((122233/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c346 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((346 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((917079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58464387/20000000 : ℚ) : ℝ) ≤ Real.log ((346 : ℕ)) / 2 := by
    have h := (log_br_346).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((346 : ℕ)) / 2 ≤ ((14616097/5000000 : ℚ) : ℝ) := by
    have h := (log_br_346).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -51263/500000) (δ := 11401/1000000000) (ψ := -125063/500000) 449 209
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t346 : ((492997541487/10000000000000 : ℚ) : ℝ) ≤ stT449o2 346 := by
  have hc : ((917029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((346 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((492997541487/10000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((917029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c347 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((347 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((485929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58493247/20000000 : ℚ) : ℝ) ≤ Real.log ((347 : ℕ)) / 2 := by
    have h := (log_br_347).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((347 : ℕ)) / 2 ≤ ((913957/312500 : ℚ) : ℝ) := by
    have h := (log_br_347).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 148627/2500000) (δ := 2813/250000000) (ψ := -125063/500000) 449 209
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t347 : ((4075732383/78125000000 : ℚ) : ℝ) ≤ stT449o2 347 := by
  have hc : ((30369/31250 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((347 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4075732383/78125000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((30369/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c348 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((348 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((317091/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7315253/2500000 : ℚ) : ℝ) ≤ Real.log ((348 : ℕ)) / 2 := by
    have h := (log_br_348).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((348 : ℕ)) / 2 ≤ ((2340881/800000 : ℚ) : ℝ) := by
    have h := (log_br_348).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2209617/10000000) (δ := 11251/1000000000) (ψ := -125063/500000) 449 209
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t348 : ((10622820731/312500000000 : ℚ) : ℝ) ≤ stT449o2 348 := by
  have hc : ((158533/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((348 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10622820731/312500000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((158533/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c349 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((349 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((21367/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58550719/20000000 : ℚ) : ℝ) ≤ Real.log ((349 : ℕ)) / 2 := by
    have h := (log_br_349).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((349 : ℕ)) / 2 ≤ ((182971/62500 : ℚ) : ℝ) := by
    have h := (log_br_349).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 955031/2500000) (δ := 2813/250000000) (ψ := -125063/500000) 449 209
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t349 : ((5712047577/2500000000000 : ℚ) : ℝ) ≤ stT449o2 349 := by
  have hc : ((10671/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((349 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5712047577/2500000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((10671/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c350 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((350 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-282153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58579331/20000000 : ℚ) : ℝ) ≤ Real.log ((350 : ℕ)) / 2 := by
    have h := (log_br_350).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((350 : ℕ)) / 2 ≤ ((14644833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_350).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1356493/2500000) (δ := 11401/1000000000) (ψ := -125063/500000) 449 209
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t350 : ((-75415315547/2500000000000 : ℚ) : ℝ) ≤ stT449o2 350 := by
  have hc : ((-141089/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((350 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75415315547/2500000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-141089/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c351 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((351 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-945821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29303931/10000000 : ℚ) : ℝ) ≤ Real.log ((351 : ℕ)) / 2 := by
    have h := (log_br_351).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((351 : ℕ)) / 2 ≤ ((58607863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_351).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 281091/400000) (δ := 5651/500000000) (ψ := -125063/500000) 449 209
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t351 : ((-504869050831/10000000000000 : ℚ) : ℝ) ≤ stT449o2 351 := by
  have hc : ((-945871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((351 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-504869050831/10000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-945871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c352 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((352 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-952943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58636311/20000000 : ℚ) : ℝ) ≤ Real.log ((352 : ℕ)) / 2 := by
    have h := (log_br_352).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((352 : ℕ)) / 2 ≤ ((7329539/2500000 : ℚ) : ℝ) := by
    have h := (log_br_352).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1770997/2500000) (δ := 11359/1000000000) (ψ := -125063/500000) 449 210
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t352 : ((-253973587493/5000000000000 : ℚ) : ℝ) ≤ stT449o2 352 := by
  have hc : ((-952993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((352 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253973587493/5000000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-952993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c353 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((353 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-585839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1466617/500000 : ℚ) : ℝ) ≤ Real.log ((353 : ℕ)) / 2 := by
    have h := (log_br_353).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((353 : ℕ)) / 2 ≤ ((58664681/20000000 : ℚ) : ℝ) := by
    have h := (log_br_353).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2745889/5000000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 210
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t353 : ((-311837662583/10000000000000 : ℚ) : ℝ) ≤ stT449o2 353 := by
  have hc : ((-585889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((353 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-311837662583/10000000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-585889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c354 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((354 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((9173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58692969/20000000 : ℚ) : ℝ) ≤ Real.log ((354 : ℕ)) / 2 := by
    have h := (log_br_354).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((354 : ℕ)) / 2 ≤ ((5869297/2000000 : ℚ) : ℝ) := by
    have h := (log_br_354).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1952029/5000000) (δ := 11259/1000000000) (ψ := -125063/500000) 449 210
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t354 : ((2424409881/5000000000000 : ℚ) : ℝ) ≤ stT449o2 354 := by
  have hc : ((9123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((354 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2424409881/5000000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((9123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c355 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((355 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((599153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58721177/20000000 : ℚ) : ℝ) ≤ Real.log ((355 : ℕ)) / 2 := by
    have h := (log_br_355).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((355 : ℕ)) / 2 ≤ ((29360589/10000000 : ℚ) : ℝ) := by
    have h := (log_br_355).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -580221/2500000) (δ := 11259/1000000000) (ψ := -125063/500000) 449 210
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t355 : ((39746290329/1250000000000 : ℚ) : ℝ) ≤ stT449o2 355 := by
  have hc : ((599103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((355 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39746290329/1250000000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((599103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c356 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((356 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((956267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58749307/20000000 : ℚ) : ℝ) ≤ Real.log ((356 : ℕ)) / 2 := by
    have h := (log_br_356).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((356 : ℕ)) / 2 ≤ ((14687327/5000000 : ℚ) : ℝ) := by
    have h := (log_br_356).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -92761/1250000) (δ := 5647/500000000) (ψ := -125063/500000) 449 210
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t356 : ((253396548783/5000000000000 : ℚ) : ℝ) ≤ stT449o2 356 := by
  have hc : ((956217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((356 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253396548783/5000000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((956217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c357 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((357 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((945103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58777357/20000000 : ℚ) : ℝ) ≤ Real.log ((357 : ℕ)) / 2 := by
    have h := (log_br_357).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((357 : ℕ)) / 2 ≤ ((29388679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_357).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 416109/5000000) (δ := 5697/500000000) (ψ := -125063/500000) 449 210
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t357 : ((62521871321/1250000000000 : ℚ) : ℝ) ≤ stT449o2 357 := by
  have hc : ((945053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((357 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62521871321/1250000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((945053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c358 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((358 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((35801/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58805329/20000000 : ℚ) : ℝ) ≤ Real.log ((358 : ℕ)) / 2 := by
    have h := (log_br_358).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((358 : ℕ)) / 2 ≤ ((5880533/2000000 : ℚ) : ℝ) := by
    have h := (log_br_358).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2402147/10000000) (δ := 11259/1000000000) (ψ := -125063/500000) 449 210
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t358 : ((37839499407/1250000000000 : ℚ) : ℝ) ≤ stT449o2 358 := by
  have hc : ((286383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((358 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37839499407/1250000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((286383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c359 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((359 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-8141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58833223/20000000 : ℚ) : ℝ) ≤ Real.log ((359 : ℕ)) / 2 := by
    have h := (log_br_359).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((359 : ℕ)) / 2 ≤ ((7354153/2500000 : ℚ) : ℝ) := by
    have h := (log_br_359).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1983849/5000000) (δ := 11359/1000000000) (ψ := -125063/500000) 449 210
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t359 : ((-107746287/125000000000 : ℚ) : ℝ) ≤ stT449o2 359 := by
  have hc : ((-4083/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((359 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107746287/125000000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-4083/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c360 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((360 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-74727/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((735763/250000 : ℚ) : ℝ) ≤ Real.log ((360 : ℕ)) / 2 := by
    have h := (log_br_360).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((360 : ℕ)) / 2 ≤ ((58861041/20000000 : ℚ) : ℝ) := by
    have h := (log_br_360).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5528927/10000000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 210
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t360 : ((-157551740851/5000000000000 : ℚ) : ℝ) ≤ stT449o2 360 := by
  have hc : ((-298933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((360 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157551740851/5000000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-298933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c361 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((361 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-953159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58888779/20000000 : ℚ) : ℝ) ≤ Real.log ((361 : ℕ)) / 2 := by
    have h := (log_br_361).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((361 : ℕ)) / 2 ≤ ((2944439/1000000 : ℚ) : ℝ) := by
    have h := (log_br_361).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3542889/5000000) (δ := 5647/500000000) (ψ := -125063/500000) 449 210
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t361 : ((-125422287011/2500000000000 : ℚ) : ℝ) ≤ stT449o2 361 := by
  have hc : ((-953209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((361 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).2
  have h0 : (0:ℝ) ≤ ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125422287011/2500000000000 : ℚ) : ℝ)
      = ((131579/2500000 : ℚ) : ℝ) * ((-953209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c362 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((362 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-475591/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29458221/10000000 : ℚ) : ℝ) ≤ Real.log ((362 : ℕ)) / 2 := by
    have h := (log_br_362).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((362 : ℕ)) / 2 ≤ ((58916443/20000000 : ℚ) : ℝ) := by
    have h := (log_br_362).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7069599/10000000) (δ := 2829/250000000) (ψ := -125063/500000) 449 211
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t362 : ((-7811829307/156250000000 : ℚ) : ℝ) ≤ stT449o2 362 := by
  have hc : ((-14863/15625 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((362 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7811829307/156250000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-14863/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c363 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((363 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-595379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14736007/5000000 : ℚ) : ℝ) ≤ Real.log ((363 : ℕ)) / 2 := by
    have h := (log_br_363).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((363 : ℕ)) / 2 ≤ ((58944029/20000000 : ℚ) : ℝ) := by
    have h := (log_br_363).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1104267/2000000) (δ := 11237/1000000000) (ψ := -125063/500000) 449 211
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t363 : ((-4883113229/156250000000 : ℚ) : ℝ) ≤ stT449o2 363 := by
  have hc : ((-595429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((363 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4883113229/156250000000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-595429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c364 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((364 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-20137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29485769/10000000 : ℚ) : ℝ) ≤ Real.log ((364 : ℕ)) / 2 := by
    have h := (log_br_364).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((364 : ℕ)) / 2 ≤ ((58971539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_364).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -497167/1250000) (δ := 2829/250000000) (ψ := -125063/500000) 449 211
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t364 : ((-10580874741/10000000000000 : ℚ) : ℝ) ≤ stT449o2 364 := by
  have hc : ((-20187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((364 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10580874741/10000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-20187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c365 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((365 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((8768/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58998973/20000000 : ℚ) : ℝ) ≤ Real.log ((365 : ℕ)) / 2 := by
    have h := (log_br_365).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((365 : ℕ)) / 2 ≤ ((29499487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_365).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2437547/10000000) (δ := 11287/1000000000) (ψ := -125063/500000) 449 211
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t365 : ((146846846073/5000000000000 : ℚ) : ℝ) ≤ stT449o2 365 := by
  have hc : ((280551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((365 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).1
  have hw2 : ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((523423/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146846846073/5000000000000 : ℚ) : ℝ)
      = ((523423/10000000 : ℚ) : ℝ) * ((280551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c366 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((366 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((935619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59026333/20000000 : ℚ) : ℝ) ≤ Real.log ((366 : ℕ)) / 2 := by
    have h := (log_br_366).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((366 : ℕ)) / 2 ≤ ((29513167/10000000 : ℚ) : ℝ) := by
    have h := (log_br_366).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -901967/10000000) (δ := 11287/1000000000) (ψ := -125063/500000) 449 211
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t366 : ((122257350213/2500000000000 : ℚ) : ℝ) ≤ stT449o2 366 := by
  have hc : ((935569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((366 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122257350213/2500000000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((935569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c367 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((367 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((38739/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29526809/10000000 : ℚ) : ℝ) ≤ Real.log ((367 : ℕ)) / 2 := by
    have h := (log_br_367).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((367 : ℕ)) / 2 ≤ ((59053619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_367).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 157351/2500000) (δ := 2829/250000000) (ψ := -125063/500000) 449 211
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t367 : ((4044104063/80000000000 : ℚ) : ℝ) ≤ stT449o2 367 := by
  have hc : ((38737/40000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((367 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4044104063/80000000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((38737/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c368 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((368 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((162607/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59080829/20000000 : ℚ) : ℝ) ≤ Real.log ((368 : ℕ)) / 2 := by
    have h := (log_br_368).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((368 : ℕ)) / 2 ≤ ((5908083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_368).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2156621/10000000) (δ := 11287/1000000000) (ψ := -125063/500000) 449 211
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t368 : ((84758236527/2500000000000 : ℚ) : ℝ) ≤ stT449o2 368 := by
  have hc : ((325189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((368 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84758236527/2500000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((325189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c369 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((369 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((98761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29553983/10000000 : ℚ) : ℝ) ≤ Real.log ((369 : ℕ)) / 2 := by
    have h := (log_br_369).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((369 : ℕ)) / 2 ≤ ((59107967/20000000 : ℚ) : ℝ) := by
    have h := (log_br_369).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 735937/2000000) (δ := 11337/1000000000) (ψ := -125063/500000) 449 211
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t369 : ((51386873669/10000000000000 : ℚ) : ℝ) ≤ stT449o2 369 := by
  have hc : ((98711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((369 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51386873669/10000000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((98711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c370 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((370 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-487011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5913503/2000000 : ℚ) : ℝ) ≤ Real.log ((370 : ℕ)) / 2 := by
    have h := (log_br_370).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((370 : ℕ)) / 2 ≤ ((59135031/20000000 : ℚ) : ℝ) := by
    have h := (log_br_370).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1299663/2500000) (δ := 11337/1000000000) (ψ := -125063/500000) 449 211
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t370 : ((-63302831109/2500000000000 : ℚ) : ℝ) ≤ stT449o2 370 := by
  have hc : ((-487061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((370 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63302831109/2500000000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-487061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c371 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((371 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-89773/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2958101/1000000 : ℚ) : ℝ) ≤ Real.log ((371 : ℕ)) / 2 := by
    have h := (log_br_371).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((371 : ℕ)) / 2 ≤ ((59162021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_371).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3356733/5000000) (δ := 11237/1000000000) (ψ := -125063/500000) 449 211
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t371 : ((-932209863/20000000000 : ℚ) : ℝ) ≤ stT449o2 371 := by
  have hc : ((-44889/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((371 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-932209863/20000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-44889/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c372 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((372 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-989053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29594469/10000000 : ℚ) : ℝ) ≤ Real.log ((372 : ℕ)) / 2 := by
    have h := (log_br_372).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((372 : ℕ)) / 2 ≤ ((59188939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_372).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1870931/2500000) (δ := 357/31250000) (ψ := -125063/500000) 449 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t372 : ((-128206541757/2500000000000 : ℚ) : ℝ) ≤ stT449o2 372 := by
  have hc : ((-989103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((372 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128206541757/2500000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-989103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c373 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((373 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-365573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7401973/2500000 : ℚ) : ℝ) ≤ Real.log ((373 : ℕ)) / 2 := by
    have h := (log_br_373).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((373 : ℕ)) / 2 ≤ ((11843157/4000000 : ℚ) : ℝ) := by
    have h := (log_br_373).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5976993/10000000) (δ := 11329/1000000000) (ψ := -125063/500000) 449 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t373 : ((-94649849019/2500000000000 : ℚ) : ℝ) ≤ stT449o2 373 := by
  have hc : ((-182799/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((373 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94649849019/2500000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-182799/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c374 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((374 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-108601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59242557/20000000 : ℚ) : ℝ) ≤ Real.log ((374 : ℕ)) / 2 := by
    have h := (log_br_374).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((374 : ℕ)) / 2 ≤ ((29621279/10000000 : ℚ) : ℝ) := by
    have h := (log_br_374).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2237179/5000000) (δ := 5637/500000000) (ψ := -125063/500000) 449 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t374 : ((-877643767/78125000000 : ℚ) : ℝ) ≤ stT449o2 374 := by
  have hc : ((-54313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((374 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-877643767/78125000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-54313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c375 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((375 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((185709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2963463/1000000 : ℚ) : ℝ) ≤ Real.log ((375 : ℕ)) / 2 := by
    have h := (log_br_375).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((375 : ℕ)) / 2 ≤ ((59269261/20000000 : ℚ) : ℝ) := by
    have h := (log_br_375).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -743913/2500000) (δ := 2831/250000000) (ψ := -125063/500000) 449 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t375 : ((23971665137/1250000000000 : ℚ) : ℝ) ≤ stT449o2 375 := by
  have hc : ((46421/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((375 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23971665137/1250000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((46421/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c376 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((376 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((414803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59295891/20000000 : ℚ) : ℝ) ≤ Real.log ((376 : ℕ)) / 2 := by
    have h := (log_br_376).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((376 : ℕ)) / 2 ≤ ((14823973/5000000 : ℚ) : ℝ) := by
    have h := (log_br_376).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1480987/10000000) (δ := 5687/500000000) (ψ := -125063/500000) 449 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t376 : ((10695258119/250000000000 : ℚ) : ℝ) ≤ stT449o2 376 := by
  have hc : ((207389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((376 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10695258119/250000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((207389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c377 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((377 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((124999/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59322451/20000000 : ℚ) : ℝ) ≤ Real.log ((377 : ℕ)) / 2 := by
    have h := (log_br_377).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((377 : ℕ)) / 2 ≤ ((14830613/5000000 : ℚ) : ℝ) := by
    have h := (log_br_377).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 9693/10000000) (δ := 5687/500000000) (ψ := -125063/500000) 449 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t377 : ((128749032123/2500000000000 : ℚ) : ℝ) ≤ stT449o2 377 := by
  have hc : ((499971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((377 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128749032123/2500000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((499971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c378 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((378 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((413069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59348941/20000000 : ℚ) : ℝ) ≤ Real.log ((378 : ℕ)) / 2 := by
    have h := (log_br_378).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((378 : ℕ)) / 2 ≤ ((29674471/10000000 : ℚ) : ℝ) := by
    have h := (log_br_378).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 374111/2500000) (δ := 5637/500000000) (ψ := -125063/500000) 449 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t378 : ((6638959473/156250000000 : ℚ) : ℝ) ≤ stT449o2 378 := by
  have hc : ((103261/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((378 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6638959473/156250000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((103261/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c379 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((379 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((185027/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29687681/10000000 : ℚ) : ℝ) ≤ Real.log ((379 : ℕ)) / 2 := by
    have h := (log_br_379).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((379 : ℕ)) / 2 ≤ ((59375363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_379).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2979323/10000000) (δ := 357/31250000) (ψ := -125063/500000) 449 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t379 : ((9502905233/500000000000 : ℚ) : ℝ) ≤ stT449o2 379 := by
  have hc : ((92501/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((379 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9502905233/500000000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((92501/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c380 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((380 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-42179/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3712607/1250000 : ℚ) : ℝ) ≤ Real.log ((380 : ℕ)) / 2 := by
    have h := (log_br_380).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((380 : ℕ)) / 2 ≤ ((59401713/20000000 : ℚ) : ℝ) := by
    have h := (log_br_380).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 557277/1250000) (δ := 11329/1000000000) (ψ := -125063/500000) 449 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t380 : ((-2164253511/200000000000 : ℚ) : ℝ) ≤ stT449o2 380 := by
  have hc : ((-42189/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((380 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2164253511/200000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-42189/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c381 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((381 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-143819/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59427993/20000000 : ℚ) : ℝ) ≤ Real.log ((381 : ℕ)) / 2 := by
    have h := (log_br_381).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((381 : ℕ)) / 2 ≤ ((29713997/10000000 : ℚ) : ℝ) := by
    have h := (log_br_381).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5933237/10000000) (δ := 11379/1000000000) (ψ := -125063/500000) 449 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t381 : ((-18421474491/500000000000 : ℚ) : ℝ) ≤ stT449o2 381 := by
  have hc : ((-143829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((381 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18421474491/500000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-143829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c382 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((382 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-983877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29727103/10000000 : ℚ) : ℝ) ≤ Real.log ((382 : ℕ)) / 2 := by
    have h := (log_br_382).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((382 : ℕ)) / 2 ≤ ((59454207/20000000 : ℚ) : ℝ) := by
    have h := (log_br_382).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3702221/5000000) (δ := 11229/1000000000) (ψ := -125063/500000) 449 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t382 : ((-100684265983/2000000000000 : ℚ) : ℝ) ≤ stT449o2 382 := by
  have hc : ((-983927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((382 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100684265983/2000000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-983927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c383 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((383 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-36731/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59480349/20000000 : ℚ) : ℝ) ≤ Real.log ((383 : ℕ)) / 2 := by
    have h := (log_br_383).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((383 : ℕ)) / 2 ≤ ((1189607/400000 : ℚ) : ℝ) := by
    have h := (log_br_383).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1367249/2000000) (δ := 11381/1000000000) (ψ := -125063/500000) 449 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t383 : ((-18769718141/400000000000 : ℚ) : ℝ) ≤ stT449o2 383 := by
  have hc : ((-36733/40000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((383 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).2
  have h0 : (0:ℝ) ≤ ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18769718141/400000000000 : ℚ) : ℝ)
      = ((510977/10000000 : ℚ) : ℝ) * ((-36733/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c384 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((384 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-273299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2380257/800000 : ℚ) : ℝ) ≤ Real.log ((384 : ℕ)) / 2 := by
    have h := (log_br_384).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((384 : ℕ)) / 2 ≤ ((29753213/10000000 : ℚ) : ℝ) := by
    have h := (log_br_384).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -537273/1000000) (δ := 1409/125000000) (ψ := -125063/500000) 449 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t384 : ((-34870060941/1250000000000 : ℚ) : ℝ) ≤ stT449o2 384 := by
  have hc : ((-68331/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((384 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34870060941/1250000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-68331/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c385 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((385 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((349/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59532433/20000000 : ℚ) : ℝ) ≤ Real.log ((385 : ℕ)) / 2 := by
    have h := (log_br_385).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((385 : ℕ)) / 2 ≤ ((29766217/10000000 : ℚ) : ℝ) := by
    have h := (log_br_385).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3913031/10000000) (δ := 1409/125000000) (ψ := -125063/500000) 449 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t385 : ((1410193249/5000000000000 : ℚ) : ℝ) ≤ stT449o2 385 := by
  have hc : ((2767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((385 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1410193249/5000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((2767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c386 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((386 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((277323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59558373/20000000 : ℚ) : ℝ) ≤ Real.log ((386 : ℕ)) / 2 := by
    have h := (log_br_386).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((386 : ℕ)) / 2 ≤ ((29779187/10000000 : ℚ) : ℝ) := by
    have h := (log_br_386).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -614287/2500000) (δ := 11381/1000000000) (ψ := -125063/500000) 449 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t386 : ((35285199957/1250000000000 : ℚ) : ℝ) ≤ stT449o2 386 := by
  have hc : ((138649/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((386 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35285199957/1250000000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((138649/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c387 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((387 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((230069/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29792123/10000000 : ℚ) : ℝ) ≤ Real.log ((387 : ℕ)) / 2 := by
    have h := (log_br_387).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((387 : ℕ)) / 2 ≤ ((59584247/20000000 : ℚ) : ℝ) := by
    have h := (log_br_387).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -502513/5000000) (δ := 11331/1000000000) (ψ := -125063/500000) 449 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t387 : ((29236040133/625000000000 : ℚ) : ℝ) ≤ stT449o2 387 := by
  have hc : ((460113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((387 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).1
  have hw2 : ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((63541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29236040133/625000000000 : ℚ) : ℝ)
      = ((63541/1250000 : ℚ) : ℝ) * ((460113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c388 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((388 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((984313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59610053/20000000 : ℚ) : ℝ) ≤ Real.log ((388 : ℕ)) / 2 := by
    have h := (log_br_388).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((388 : ℕ)) / 2 ≤ ((29805027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_388).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3464/78125) (δ := 11381/1000000000) (ψ := -125063/500000) 449 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t388 : ((499683749999/10000000000000 : ℚ) : ℝ) ≤ stT449o2 388 := by
  have hc : ((984263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((388 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499683749999/10000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((984263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c389 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((389 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((728121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59635793/20000000 : ℚ) : ℝ) ≤ Real.log ((389 : ℕ)) / 2 := by
    have h := (log_br_389).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((389 : ℕ)) / 2 ≤ ((29817897/10000000 : ℚ) : ℝ) := by
    have h := (log_br_389).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1888049/10000000) (δ := 1409/125000000) (ψ := -125063/500000) 449 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t389 : ((18457327921/500000000000 : ℚ) : ℝ) ≤ stT449o2 389 := by
  have hc : ((728071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((389 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18457327921/500000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((728071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c390 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((390 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((236921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59661467/20000000 : ℚ) : ℝ) ≤ Real.log ((390 : ℕ)) / 2 := by
    have h := (log_br_390).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((390 : ℕ)) / 2 ≤ ((14915367/5000000 : ℚ) : ℝ) := by
    have h := (log_br_390).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1664501/5000000) (δ := 2843/250000000) (ψ := -125063/500000) 449 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t390 : ((119944131399/10000000000000 : ℚ) : ℝ) ≤ stT449o2 390 := by
  have hc : ((236871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((390 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119944131399/10000000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((236871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c391 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((391 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-164717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2387483/800000 : ℚ) : ℝ) ≤ Real.log ((391 : ℕ)) / 2 := by
    have h := (log_br_391).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((391 : ℕ)) / 2 ≤ ((14921769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_391).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4766251/10000000) (δ := 2843/250000000) (ψ := -125063/500000) 449 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t391 : ((-20828413431/1250000000000 : ℚ) : ℝ) ≤ stT449o2 391 := by
  have hc : ((-82371/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((391 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).2
  have h0 : (0:ℝ) ≤ ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20828413431/1250000000000 : ℚ) : ℝ)
      = ((252861/5000000 : ℚ) : ℝ) * ((-82371/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c392 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((392 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-394489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29856309/10000000 : ℚ) : ℝ) ≤ Real.log ((392 : ℕ)) / 2 := by
    have h := (log_br_392).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((392 : ℕ)) / 2 ≤ ((59712619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_392).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1549963/2500000) (δ := 5661/500000000) (ψ := -125063/500000) 449 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t392 : ((-99629973789/2500000000000 : ℚ) : ℝ) ≤ stT449o2 392 := by
  have hc : ((-197257/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((392 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).2
  have h0 : (0:ℝ) ≤ ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99629973789/2500000000000 : ℚ) : ℝ)
      = ((505077/10000000 : ℚ) : ℝ) * ((-197257/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c393 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((393 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-497991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3733631/1250000 : ℚ) : ℝ) ≤ Real.log ((393 : ℕ)) / 2 := by
    have h := (log_br_393).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((393 : ℕ)) / 2 ≤ ((59738097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_393).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1525961/2000000) (δ := 11231/1000000000) (ψ := -125063/500000) 449 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t393 : ((-3925253171/78125000000 : ℚ) : ℝ) ≤ stT449o2 393 := by
  have hc : ((-15563/15625 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((393 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3925253171/78125000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-15563/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c394 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((394 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-443301/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59763509/20000000 : ℚ) : ℝ) ≤ Real.log ((394 : ℕ)) / 2 := by
    have h := (log_br_394).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((394 : ℕ)) / 2 ≤ ((5976351/2000000 : ℚ) : ℝ) := by
    have h := (log_br_394).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3325927/5000000) (δ := 2273/200000000) (ψ := -125063/500000) 449 214
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t394 : ((-111672267759/2500000000000 : ℚ) : ℝ) ≤ stT449o2 394 := by
  have hc : ((-221663/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((394 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111672267759/2500000000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-221663/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c395 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((395 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-248823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59788857/20000000 : ℚ) : ℝ) ≤ Real.log ((395 : ℕ)) / 2 := by
    have h := (log_br_395).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((395 : ℕ)) / 2 ≤ ((29894429/10000000 : ℚ) : ℝ) := by
    have h := (log_br_395).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5229197/10000000) (δ := 1411/125000000) (ψ := -125063/500000) 449 214
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t395 : ((-1565113943/62500000000 : ℚ) : ℝ) ≤ stT449o2 395 := by
  have hc : ((-15553/31250 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((395 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1565113943/62500000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-15553/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c396 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((396 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((11687/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29907071/10000000 : ℚ) : ℝ) ≤ Real.log ((396 : ℕ)) / 2 := by
    have h := (log_br_396).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((396 : ℕ)) / 2 ≤ ((59814143/20000000 : ℚ) : ℝ) := by
    have h := (log_br_396).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3810077/10000000) (δ := 2283/200000000) (ψ := -125063/500000) 449 214
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t396 : ((5866646391/2500000000000 : ℚ) : ℝ) ≤ stT449o2 396 := by
  have hc : ((23349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((396 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5866646391/2500000000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((23349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c397 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((397 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((575287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29919681/10000000 : ℚ) : ℝ) ≤ Real.log ((397 : ℕ)) / 2 := by
    have h := (log_br_397).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((397 : ℕ)) / 2 ≤ ((59839363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_397).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -598651/2500000) (δ := 5619/500000000) (ψ := -125063/500000) 449 214
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t397 : ((57740564349/2000000000000 : ℚ) : ℝ) ≤ stT449o2 397 := by
  have hc : ((575237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((397 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).1
  have hw2 : ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((100377/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57740564349/2000000000000 : ℚ) : ℝ)
      = ((100377/2000000 : ℚ) : ℝ) * ((575237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c398 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((398 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((923747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1496613/500000 : ℚ) : ℝ) ≤ Real.log ((398 : ℕ)) / 2 := by
    have h := (log_br_398).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((398 : ℕ)) / 2 ≤ ((59864521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_398).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -982611/10000000) (δ := 5669/500000000) (ψ := -125063/500000) 449 214
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t398 : ((231503408019/5000000000000 : ℚ) : ℝ) ≤ stT449o2 398 := by
  have hc : ((923697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((398 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231503408019/5000000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((923697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c399 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((399 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((985531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29944807/10000000 : ℚ) : ℝ) ≤ Real.log ((399 : ℕ)) / 2 := by
    have h := (log_br_399).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((399 : ℕ)) / 2 ≤ ((11977923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_399).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 425789/10000000) (δ := 2283/200000000) (ψ := -125063/500000) 449 214
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t399 : ((246678705553/5000000000000 : ℚ) : ℝ) ≤ stT449o2 399 := by
  have hc : ((985481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((399 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246678705553/5000000000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((985481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c400 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((400 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((46479/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11982929/4000000 : ℚ) : ℝ) ≤ Real.log ((400 : ℕ)) / 2 := by
    have h := (log_br_400).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((400 : ℕ)) / 2 ≤ ((29957323/10000000 : ℚ) : ℝ) := by
    have h := (log_br_400).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 915327/5000000) (δ := 2273/200000000) (ψ := -125063/500000) 449 214
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t400 : ((371807/10000000 : ℚ) : ℝ) ≤ stT449o2 400 := by
  have hc : ((371807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((400 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((371807/10000000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((371807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c401 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((401 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((137207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29969807/10000000 : ℚ) : ℝ) ≤ Real.log ((401 : ℕ)) / 2 := by
    have h := (log_br_401).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((401 : ℕ)) / 2 ≤ ((11987923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_401).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3232039/10000000) (δ := 2283/200000000) (ψ := -125063/500000) 449 214
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t401 : ((2140793701/156250000000 : ℚ) : ℝ) ≤ stT449o2 401 := by
  have hc : ((68591/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((401 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2140793701/156250000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((68591/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c402 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((402 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-27747/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1499113/500000 : ℚ) : ℝ) ≤ Real.log ((402 : ℕ)) / 2 := by
    have h := (log_br_402).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((402 : ℕ)) / 2 ≤ ((59964521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_402).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4629889/10000000) (δ := 5669/500000000) (ψ := -125063/500000) 449 214
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t402 : ((-346036219/25000000000 : ℚ) : ℝ) ≤ stT449o2 402 := by
  have hc : ((-3469/12500 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((402 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-346036219/25000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-3469/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c403 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((403 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-92991/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11997873/4000000 : ℚ) : ℝ) ≤ Real.log ((403 : ℕ)) / 2 := by
    have h := (log_br_403).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((403 : ℕ)) / 2 ≤ ((29994683/10000000 : ℚ) : ℝ) := by
    have h := (log_br_403).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3012157/5000000) (δ := 2273/200000000) (ψ := -125063/500000) 449 214
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t403 : ((-23162639063/625000000000 : ℚ) : ℝ) ≤ stT449o2 403 := by
  have hc : ((-371989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((403 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23162639063/625000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-371989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c404 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((404 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-984641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15003537/5000000 : ℚ) : ℝ) ≤ Real.log ((404 : ℕ)) / 2 := by
    have h := (log_br_404).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((404 : ℕ)) / 2 ≤ ((60014149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_404).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 370763/500000) (δ := 2263/200000000) (ψ := -125063/500000) 449 214
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t404 : ((-489902481629/10000000000000 : ℚ) : ℝ) ≤ stT449o2 404 := by
  have hc : ((-984691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((404 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-489902481629/10000000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-984691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c405 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((405 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-464421/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6003887/2000000 : ℚ) : ℝ) ≤ Real.log ((405 : ℕ)) / 2 := by
    have h := (log_br_405).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((405 : ℕ)) / 2 ≤ ((60038871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_405).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6905181/10000000) (δ := 2827/250000000) (ψ := -125063/500000) 449 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t405 : ((-14424067199/312500000000 : ℚ) : ℝ) ≤ stT449o2 405 := by
  have hc : ((-232223/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((405 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14424067199/312500000000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-232223/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c406 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((406 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-297649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60063531/20000000 : ℚ) : ℝ) ≤ Real.log ((406 : ℕ)) / 2 := by
    have h := (log_br_406).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((406 : ℕ)) / 2 ≤ ((15015883/5000000 : ℚ) : ℝ) := by
    have h := (log_br_406).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2760541/5000000) (δ := 2259/200000000) (ψ := -125063/500000) 449 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t406 : ((-18466653101/625000000000 : ℚ) : ℝ) ≤ stT449o2 406 := by
  have hc : ((-148837/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((406 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18466653101/625000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-148837/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c407 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((407 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-85263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60088131/20000000 : ℚ) : ℝ) ≤ Real.log ((407 : ℕ)) / 2 := by
    have h := (log_br_407).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((407 : ℕ)) / 2 ≤ ((15022033/5000000 : ℚ) : ℝ) := by
    have h := (log_br_407).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4140407/10000000) (δ := 2259/200000000) (ψ := -125063/500000) 449 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t407 : ((-21144059233/5000000000000 : ℚ) : ℝ) ≤ stT449o2 407 := by
  have hc : ((-85313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((407 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21144059233/5000000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-85313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c408 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((408 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((11223/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60112671/20000000 : ℚ) : ℝ) ≤ Real.log ((408 : ℕ)) / 2 := by
    have h := (log_br_408).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((408 : ℕ)) / 2 ≤ ((1878521/625000 : ℚ) : ℝ) := by
    have h := (log_br_408).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -27631/100000) (δ := 5679/500000000) (ψ := -125063/500000) 449 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t408 : ((22222341751/1000000000000 : ℚ) : ℝ) ≤ stT449o2 408 := by
  have hc : ((44887/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((408 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22222341751/1000000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((44887/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c409 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((409 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((16991/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60137151/20000000 : ℚ) : ℝ) ≤ Real.log ((409 : ℕ)) / 2 := by
    have h := (log_br_409).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((409 : ℕ)) / 2 ≤ ((939643/312500 : ℚ) : ℝ) := by
    have h := (log_br_409).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -34729/250000) (δ := 5679/500000000) (ψ := -125063/500000) 449 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t409 : ((210025283/5000000000 : ℚ) : ℝ) ≤ stT449o2 409 := by
  have hc : ((1699/2000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((409 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210025283/5000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((1699/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c410 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((410 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((249993/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60161571/20000000 : ℚ) : ℝ) ≤ Real.log ((410 : ℕ)) / 2 := by
    have h := (log_br_410).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((410 : ℕ)) / 2 ≤ ((15040393/5000000 : ℚ) : ℝ) := by
    have h := (log_br_410).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -18587/10000000) (δ := 2259/200000000) (ψ := -125063/500000) 449 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t410 : ((30864092413/625000000000 : ℚ) : ℝ) ≤ stT449o2 410 := by
  have hc : ((499961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((410 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30864092413/625000000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((499961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c411 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((411 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((857981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15046483/5000000 : ℚ) : ℝ) ≤ Real.log ((411 : ℕ)) / 2 := by
    have h := (log_br_411).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((411 : ℕ)) / 2 ≤ ((60185933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_411).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 674337/5000000) (δ := 2249/200000000) (ψ := -125063/500000) 449 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t411 : ((423185618853/10000000000000 : ℚ) : ℝ) ≤ stT449o2 411 := by
  have hc : ((857931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((411 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((423185618853/10000000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((857931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c412 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((412 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((466889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60210233/20000000 : ℚ) : ℝ) ≤ Real.log ((412 : ℕ)) / 2 := by
    have h := (log_br_412).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((412 : ℕ)) / 2 ≤ ((30105117/10000000 : ℚ) : ℝ) := by
    have h := (log_br_412).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 339071/1250000) (δ := 2279/200000000) (ψ := -125063/500000) 449 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t412 : ((28749346137/1250000000000 : ℚ) : ℝ) ≤ stT449o2 412 := by
  have hc : ((466839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((412 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28749346137/1250000000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((466839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c413 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((413 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-5843/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2409379/800000 : ℚ) : ℝ) ≤ Real.log ((413 : ℕ)) / 2 := by
    have h := (log_br_413).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((413 : ℕ)) / 2 ≤ ((15058619/5000000 : ℚ) : ℝ) := by
    have h := (log_br_413).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 81463/200000) (δ := 2259/200000000) (ψ := -125063/500000) 449 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t413 : ((-89925427/31250000000 : ℚ) : ℝ) ≤ stT449o2 413 := by
  have hc : ((-731/12500 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((413 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89925427/31250000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-731/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c414 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((414 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-565793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60258659/20000000 : ℚ) : ℝ) ≤ Real.log ((414 : ℕ)) / 2 := by
    have h := (log_br_414).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((414 : ℕ)) / 2 ≤ ((3012933/1000000 : ℚ) : ℝ) := by
    have h := (log_br_414).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5430477/10000000) (δ := 2259/200000000) (ψ := -125063/500000) 449 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t414 : ((-139048561291/5000000000000 : ℚ) : ℝ) ≤ stT449o2 414 := by
  have hc : ((-565843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((414 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139048561291/5000000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-565843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c415 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((415 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-227473/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12056557/4000000 : ℚ) : ℝ) ≤ Real.log ((415 : ℕ)) / 2 := by
    have h := (log_br_415).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((415 : ℕ)) / 2 ≤ ((30141393/10000000 : ℚ) : ℝ) := by
    have h := (log_br_415).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6784549/10000000) (δ := 2279/200000000) (ψ := -125063/500000) 449 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t415 : ((-223336619451/5000000000000 : ℚ) : ℝ) ≤ stT449o2 415 := by
  have hc : ((-454971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((415 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223336619451/5000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-454971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c416 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((416 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-39747/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15076713/5000000 : ℚ) : ℝ) ≤ Real.log ((416 : ℕ)) / 2 := by
    have h := (log_br_416).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((416 : ℕ)) / 2 ≤ ((60306853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_416).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3786327/5000000) (δ := 1419/125000000) (ψ := -125063/500000) 449 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t416 : ((-19488576959/400000000000 : ℚ) : ℝ) ≤ stT449o2 416 := by
  have hc : ((-39749/40000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((416 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19488576959/400000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-39749/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c417 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((417 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-795141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30165431/10000000 : ℚ) : ℝ) ≤ Real.log ((417 : ℕ)) / 2 := by
    have h := (log_br_417).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((417 : ℕ)) / 2 ≤ ((60330863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_417).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6225093/10000000) (δ := 2813/250000000) (ψ := -125063/500000) 449 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t417 : ((-389407418273/10000000000000 : ℚ) : ℝ) ≤ stT449o2 417 := by
  have hc : ((-795191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((417 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-389407418273/10000000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-795191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c418 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((418 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-37233/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30177407/10000000 : ℚ) : ℝ) ≤ Real.log ((418 : ℕ)) / 2 := by
    have h := (log_br_418).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((418 : ℕ)) / 2 ≤ ((12070963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_418).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4880787/10000000) (δ := 2813/250000000) (ψ := -125063/500000) 449 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t418 : ((-2276712701/125000000000 : ℚ) : ℝ) ≤ stT449o2 418 := by
  have hc : ((-18619/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((418 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2276712701/125000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-18619/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c419 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((419 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((30861/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60378709/20000000 : ℚ) : ℝ) ≤ Real.log ((419 : ℕ)) / 2 := by
    have h := (log_br_419).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((419 : ℕ)) / 2 ≤ ((6037871/2000000 : ℚ) : ℝ) := by
    have h := (log_br_419).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -22123/62500) (δ := 5651/500000000) (ψ := -125063/500000) 449 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t419 : ((15071669881/2000000000000 : ℚ) : ℝ) ≤ stT449o2 419 := by
  have hc : ((30851/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((419 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15071669881/2000000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((30851/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c420 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((420 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((127321/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60402547/20000000 : ℚ) : ℝ) ≤ Real.log ((420 : ℕ)) / 2 := by
    have h := (log_br_420).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((420 : ℕ)) / 2 ≤ ((15100637/5000000 : ℚ) : ℝ) := by
    have h := (log_br_420).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -550443/2500000) (δ := 5701/500000000) (ψ := -125063/500000) 449 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t420 : ((1242428049/40000000000 : ℚ) : ℝ) ≤ stT449o2 420 := by
  have hc : ((127311/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((420 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1242428049/40000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((127311/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c421 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((421 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((117557/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7553291/2500000 : ℚ) : ℝ) ≤ Real.log ((421 : ℕ)) / 2 := by
    have h := (log_br_421).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((421 : ℕ)) / 2 ≤ ((60426329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_421).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -108383/1250000) (δ := 11301/1000000000) (ψ := -125063/500000) 449 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t421 : ((22916283611/500000000000 : ℚ) : ℝ) ≤ stT449o2 421 := by
  have hc : ((470203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((421 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22916283611/500000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((470203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c422 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((422 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((982789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60450053/20000000 : ℚ) : ℝ) ≤ Real.log ((422 : ℕ)) / 2 := by
    have h := (log_br_422).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((422 : ℕ)) / 2 ≤ ((30225027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_422).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 232251/5000000) (δ := 5651/500000000) (ψ := -125063/500000) 449 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t422 : ((59798685411/1250000000000 : ℚ) : ℝ) ≤ stT449o2 422 := by
  have hc : ((982739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((422 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59798685411/1250000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((982739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c423 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((423 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((188421/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60473721/20000000 : ℚ) : ℝ) ≤ Real.log ((423 : ℕ)) / 2 := by
    have h := (log_br_423).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((423 : ℕ)) / 2 ≤ ((30236861/10000000 : ℚ) : ℝ) := by
    have h := (log_br_423).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 448217/2500000) (δ := 11351/1000000000) (ψ := -125063/500000) 449 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t423 : ((22901806809/625000000000 : ℚ) : ℝ) ≤ stT449o2 423 := by
  have hc : ((376817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((423 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22901806809/625000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((376817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c424 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((424 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((158961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30248667/10000000 : ℚ) : ℝ) ≤ Real.log ((424 : ℕ)) / 2 := by
    have h := (log_br_424).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((424 : ℕ)) / 2 ≤ ((12099467/4000000 : ℚ) : ℝ) := by
    have h := (log_br_424).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 779537/2500000) (δ := 2813/250000000) (ψ := -125063/500000) 449 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t424 : ((4824124807/312500000000 : ℚ) : ℝ) ≤ stT449o2 424 := by
  have hc : ((19867/62500 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((424 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4824124807/312500000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((19867/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c425 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((425 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-101939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60520891/20000000 : ℚ) : ℝ) ≤ Real.log ((425 : ℕ)) / 2 := by
    have h := (log_br_425).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((425 : ℕ)) / 2 ≤ ((15130223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_425).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 888057/2000000) (δ := 5701/500000000) (ψ := -125063/500000) 449 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t425 : ((-772810647/78125000000 : ℚ) : ℝ) ≤ stT449o2 425 := by
  have hc : ((-25491/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((425 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-772810647/78125000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-25491/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c426 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((426 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-10454/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60544393/20000000 : ℚ) : ℝ) ≤ Real.log ((426 : ℕ)) / 2 := by
    have h := (log_br_426).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((426 : ℕ)) / 2 ≤ ((30272197/10000000 : ℚ) : ℝ) := by
    have h := (log_br_426).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2879667/5000000) (δ := 11351/1000000000) (ψ := -125063/500000) 449 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t426 : ((-81045798803/2500000000000 : ℚ) : ℝ) ≤ stT449o2 426 := by
  have hc : ((-334553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((426 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81045798803/2500000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-334553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c427 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((427 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-951883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((378549/125000 : ℚ) : ℝ) ≤ Real.log ((427 : ℕ)) / 2 := by
    have h := (log_br_427).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((427 : ℕ)) / 2 ≤ ((60567841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_427).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7075297/10000000) (δ := 11301/1000000000) (ψ := -125063/500000) 449 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t427 : ((-230336372211/5000000000000 : ℚ) : ℝ) ≤ stT449o2 427 := by
  have hc : ((-951933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((427 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230336372211/5000000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-951933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c428 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((428 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-977263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60591231/20000000 : ℚ) : ℝ) ≤ Real.log ((428 : ℕ)) / 2 := by
    have h := (log_br_428).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((428 : ℕ)) / 2 ≤ ((473369/156250 : ℚ) : ℝ) := by
    have h := (log_br_428).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3659923/5000000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t428 : ((-472402807497/10000000000000 : ℚ) : ℝ) ≤ stT449o2 428 := by
  have hc : ((-977313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((428 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-472402807497/10000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-977313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c429 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((429 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-74009/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60614569/20000000 : ℚ) : ℝ) ≤ Real.log ((429 : ℕ)) / 2 := by
    have h := (log_br_429).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((429 : ℕ)) / 2 ≤ ((6061457/2000000 : ℚ) : ℝ) := by
    have h := (log_br_429).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6010001/10000000) (δ := 2811/250000000) (ψ := -125063/500000) 449 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t429 : ((-3573432927/100000000000 : ℚ) : ℝ) ≤ stT449o2 429 := by
  have hc : ((-37007/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((429 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3573432927/100000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-37007/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c430 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((430 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-4774/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15159463/5000000 : ℚ) : ℝ) ≤ Real.log ((430 : ℕ)) / 2 := by
    have h := (log_br_430).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((430 : ℕ)) / 2 ≤ ((60637853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_430).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4703243/10000000) (δ := 5697/500000000) (ψ := -125063/500000) 449 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t430 : ((-73683354699/5000000000000 : ℚ) : ℝ) ≤ stT449o2 430 := by
  have hc : ((-152793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((430 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73683354699/5000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-152793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c431 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((431 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((104703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1516527/500000 : ℚ) : ℝ) ≤ Real.log ((431 : ℕ)) / 2 := by
    have h := (log_br_431).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((431 : ℕ)) / 2 ≤ ((60661081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_431).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3399571/10000000) (δ := 11259/1000000000) (ψ := -125063/500000) 449 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t431 : ((25210806537/2500000000000 : ℚ) : ℝ) ≤ stT449o2 431 := by
  have hc : ((52339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((431 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25210806537/2500000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((52339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c432 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((432 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((333899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12136851/4000000 : ℚ) : ℝ) ≤ Real.log ((432 : ℕ)) / 2 := by
    have h := (log_br_432).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((432 : ℕ)) / 2 ≤ ((1896383/625000 : ℚ) : ℝ) := by
    have h := (log_br_432).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1049437/5000000) (δ := 11309/1000000000) (ψ := -125063/500000) 449 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t432 : ((642540513/20000000000 : ℚ) : ℝ) ≤ stT449o2 432 := by
  have hc : ((166937/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((432 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((642540513/20000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((166937/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c433 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((433 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((94909/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60707377/20000000 : ℚ) : ℝ) ≤ Real.log ((433 : ℕ)) / 2 := by
    have h := (log_br_433).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((433 : ℕ)) / 2 ≤ ((30353689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_433).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6259/78125) (δ := 2811/250000000) (ψ := -125063/500000) 449 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t433 : ((5700990047/125000000000 : ℚ) : ℝ) ≤ stT449o2 433 := by
  have hc : ((11863/12500 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((433 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5700990047/125000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((11863/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c434 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((434 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((980577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12146089/4000000 : ℚ) : ℝ) ≤ Real.log ((434 : ℕ)) / 2 := by
    have h := (log_br_434).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((434 : ℕ)) / 2 ≤ ((30365223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_434).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 24677/500000) (δ := 11409/1000000000) (ψ := -125063/500000) 449 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t434 : ((94133533581/2000000000000 : ℚ) : ℝ) ≤ stT449o2 434 := by
  have hc : ((980527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((434 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94133533581/2000000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((980527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c435 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((435 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((755681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3037673/1000000 : ℚ) : ℝ) ≤ Real.log ((435 : ℕ)) / 2 := by
    have h := (log_br_435).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((435 : ℕ)) / 2 ≤ ((60753461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_435).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 223157/1250000) (δ := 5697/500000000) (ψ := -125063/500000) 449 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t435 : ((362297106153/10000000000000 : ℚ) : ℝ) ≤ stT449o2 435 := by
  have hc : ((755631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((435 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((362297106153/10000000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((755631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c436 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((436 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((66923/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30388211/10000000 : ℚ) : ℝ) ≤ Real.log ((436 : ℕ)) / 2 := by
    have h := (log_br_436).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((436 : ℕ)) / 2 ≤ ((60776423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_436).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3073999/10000000) (δ := 11359/1000000000) (ψ := -125063/500000) 449 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t436 : ((32045505569/2000000000000 : ℚ) : ℝ) ≤ stT449o2 436 := by
  have hc : ((66913/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((436 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32045505569/2000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((66913/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c437 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((437 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-172247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60799331/20000000 : ℚ) : ℝ) ≤ Real.log ((437 : ℕ)) / 2 := by
    have h := (log_br_437).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((437 : ℕ)) / 2 ≤ ((15199833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_437).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2179883/5000000) (δ := 709/62500000) (ψ := -125063/500000) 449 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t437 : ((-16484170881/2000000000000 : ℚ) : ℝ) ≤ stT449o2 437 := by
  have hc : ((-172297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((437 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16484170881/2000000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-172297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c438 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((438 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-316829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60822189/20000000 : ℚ) : ℝ) ≤ Real.log ((438 : ℕ)) / 2 := by
    have h := (log_br_438).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((438 : ℕ)) / 2 ≤ ((6082219/2000000 : ℚ) : ℝ) := by
    have h := (log_br_438).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 352667/625000) (δ := 11409/1000000000) (ψ := -125063/500000) 449 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t438 : ((-75699430713/2500000000000 : ℚ) : ℝ) ≤ stT449o2 438 := by
  have hc : ((-158427/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((438 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75699430713/2500000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-158427/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c439 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((439 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-465701/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30422497/10000000 : ℚ) : ℝ) ≤ Real.log ((439 : ℕ)) / 2 := by
    have h := (log_br_439).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((439 : ℕ)) / 2 ≤ ((12168999/4000000 : ℚ) : ℝ) := by
    have h := (log_br_439).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3461301/5000000) (δ := 5647/500000000) (ψ := -125063/500000) 449 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t439 : ((-55569727731/1250000000000 : ℚ) : ℝ) ≤ stT449o2 439 := by
  have hc : ((-232863/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((439 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55569727731/1250000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-232863/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c440 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((440 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-495229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60867747/20000000 : ℚ) : ℝ) ≤ Real.log ((440 : ℕ)) / 2 := by
    have h := (log_br_440).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((440 : ℕ)) / 2 ≤ ((15216937/5000000 : ℚ) : ℝ) := by
    have h := (log_br_440).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7508349/10000000) (δ := 2809/250000000) (ψ := -125063/500000) 449 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t440 : ((-29512928741/625000000000 : ℚ) : ℝ) ≤ stT449o2 440 := by
  have hc : ((-247627/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((440 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29512928741/625000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-247627/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c441 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((441 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-797359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3805653/1250000 : ℚ) : ℝ) ≤ Real.log ((441 : ℕ)) / 2 := by
    have h := (log_br_441).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((441 : ℕ)) / 2 ≤ ((60890449/20000000 : ℚ) : ℝ) := by
    have h := (log_br_441).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1246851/2000000) (δ := 11367/1000000000) (ψ := -125063/500000) 449 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t441 : ((-379718989119/10000000000000 : ℚ) : ℝ) ≤ stT449o2 441 := by
  have hc : ((-797409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((441 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-379718989119/10000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-797409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c442 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((442 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-402653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30456549/10000000 : ℚ) : ℝ) ≤ Real.log ((442 : ℕ)) / 2 := by
    have h := (log_br_442).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((442 : ℕ)) / 2 ≤ ((60913099/20000000 : ℚ) : ℝ) := by
    have h := (log_br_442).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -310189/625000) (δ := 11267/1000000000) (ψ := -125063/500000) 449 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t442 : ((-47886621839/2500000000000 : ℚ) : ℝ) ≤ stT449o2 442 := by
  have hc : ((-402703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((442 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47886621839/2500000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-402703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c443 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((443 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((92801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60935697/20000000 : ℚ) : ℝ) ≤ Real.log ((443 : ℕ)) / 2 := by
    have h := (log_br_443).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((443 : ℕ)) / 2 ≤ ((30467849/10000000 : ℚ) : ℝ) := by
    have h := (log_br_443).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -738931/2000000) (δ := 11317/1000000000) (ψ := -125063/500000) 449 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t443 : ((22033649307/5000000000000 : ℚ) : ℝ) ≤ stT449o2 443 := by
  have hc : ((92751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((443 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22033649307/5000000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((92751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c444 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((444 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((56393/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12191649/4000000 : ℚ) : ℝ) ≤ Real.log ((444 : ℕ)) / 2 := by
    have h := (log_br_444).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((444 : ℕ)) / 2 ≤ ((30479123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_444).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2429149/10000000) (δ := 1417/125000000) (ψ := -125063/500000) 449 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t444 : ((3345063033/125000000000 : ℚ) : ℝ) ≤ stT449o2 444 := by
  have hc : ((14097/25000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((444 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3345063033/125000000000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((14097/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c445 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((445 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((446551/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30490371/10000000 : ℚ) : ℝ) ≤ Real.log ((445 : ℕ)) / 2 := by
    have h := (log_br_445).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((445 : ℕ)) / 2 ≤ ((60980743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_445).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -233301/2000000) (δ := 5693/500000000) (ψ := -125063/500000) 449 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t445 : ((21167341767/500000000000 : ℚ) : ℝ) ≤ stT449o2 445 := by
  have hc : ((223263/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((445 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21167341767/500000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((223263/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c446 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((446 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((999303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61003189/20000000 : ℚ) : ℝ) ≤ Real.log ((446 : ℕ)) / 2 := by
    have h := (log_br_446).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((446 : ℕ)) / 2 ≤ ((6100319/2000000 : ℚ) : ℝ) := by
    have h := (log_br_446).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 93333/10000000) (δ := 1417/125000000) (ψ := -125063/500000) 449 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t446 : ((473159285789/10000000000000 : ℚ) : ℝ) ≤ stT449o2 446 := by
  have hc : ((999253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((446 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((473159285789/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((999253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c447 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((447 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((171529/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12205117/4000000 : ℚ) : ℝ) ≤ Real.log ((447 : ℕ)) / 2 := by
    have h := (log_br_447).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((447 : ℕ)) / 2 ≤ ((30512793/10000000 : ℚ) : ℝ) := by
    have h := (log_br_447).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1350309/10000000) (δ := 11317/1000000000) (ψ := -125063/500000) 449 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t447 : ((81125571177/2000000000000 : ℚ) : ℝ) ≤ stT449o2 447 := by
  have hc : ((171519/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((447 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81125571177/2000000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((171519/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c448 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((448 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((100931/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15261983/5000000 : ℚ) : ℝ) ≤ Real.log ((448 : ℕ)) / 2 := by
    have h := (log_br_448).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((448 : ℕ)) / 2 ≤ ((61047933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_448).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1302267/5000000) (δ := 5643/500000000) (ψ := -125063/500000) 449 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t448 : ((9536126211/400000000000 : ℚ) : ℝ) ≤ stT449o2 448 := by
  have hc : ((100921/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((448 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9536126211/400000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((100921/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c449 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((449 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((14217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15267557/5000000 : ℚ) : ℝ) ≤ Real.log ((449 : ℕ)) / 2 := by
    have h := (log_br_449).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((449 : ℕ)) / 2 ≤ ((61070229/20000000 : ℚ) : ℝ) := by
    have h := (log_br_449).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3855897/10000000) (δ := 5643/500000000) (ψ := -125063/500000) 449 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t449 : ((418601023/312500000000 : ℚ) : ℝ) ≤ stT449o2 449 := by
  have hc : ((887/31250 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((449 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((418601023/312500000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((887/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c450 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((450 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-56723/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2443699/800000 : ℚ) : ℝ) ≤ Real.log ((450 : ℕ)) / 2 := by
    have h := (log_br_450).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((450 : ℕ)) / 2 ≤ ((15273119/5000000 : ℚ) : ℝ) := by
    have h := (log_br_450).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 510451/1000000) (δ := 2809/250000000) (ψ := -125063/500000) 449 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t450 : ((-21393961677/1000000000000 : ℚ) : ℝ) ≤ stT449o2 450 := by
  have hc : ((-226917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((450 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21393961677/1000000000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-226917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c451 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((451 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-20613/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61114673/20000000 : ℚ) : ℝ) ≤ Real.log ((451 : ℕ)) / 2 := by
    have h := (log_br_451).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((451 : ℕ)) / 2 ≤ ((30557337/10000000 : ℚ) : ℝ) := by
    have h := (log_br_451).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6350373/10000000) (δ := 11317/1000000000) (ψ := -125063/500000) 449 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t451 : ((-19413758537/500000000000 : ℚ) : ℝ) ≤ stT449o2 451 := by
  have hc : ((-82457/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((451 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19413758537/500000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-82457/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c452 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((452 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-497287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61136821/20000000 : ℚ) : ℝ) ≤ Real.log ((452 : ℕ)) / 2 := by
    have h := (log_br_452).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((452 : ℕ)) / 2 ≤ ((30568411/10000000 : ℚ) : ℝ) := by
    have h := (log_br_452).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7593429/10000000) (δ := 1417/125000000) (ψ := -125063/500000) 449 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t452 : ((-7309880301/156250000000 : ℚ) : ℝ) ≤ stT449o2 452 := by
  have hc : ((-15541/15625 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((452 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7309880301/156250000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-15541/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c453 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((453 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-57761/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61158921/20000000 : ℚ) : ℝ) ≤ Real.log ((453 : ℕ)) / 2 := by
    have h := (log_br_453).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((453 : ℕ)) / 2 ≤ ((30579461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_453).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6874171/10000000) (δ := 357/31250000) (ψ := -125063/500000) 449 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t453 : ((-217119634033/5000000000000 : ℚ) : ℝ) ≤ stT449o2 453 := by
  have hc : ((-462113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((453 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217119634033/5000000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-462113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c454 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((454 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-315891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61180971/20000000 : ℚ) : ℝ) ≤ Real.log ((454 : ℕ)) / 2 := by
    have h := (log_br_454).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((454 : ℕ)) / 2 ≤ ((15295243/5000000 : ℚ) : ℝ) := by
    have h := (log_br_454).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1127323/2000000) (δ := 2831/250000000) (ψ := -125063/500000) 449 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t454 : ((-9266685049/312500000000 : ℚ) : ℝ) ≤ stT449o2 454 := by
  have hc : ((-78979/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((454 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9266685049/312500000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-78979/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c455 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((455 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-188743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30601487/10000000 : ℚ) : ℝ) ≤ Real.log ((455 : ℕ)) / 2 := by
    have h := (log_br_455).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((455 : ℕ)) / 2 ≤ ((2448119/800000 : ℚ) : ℝ) := by
    have h := (log_br_455).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4401697/10000000) (δ := 11279/1000000000) (ψ := -125063/500000) 449 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t455 : ((-11063458593/1250000000000 : ℚ) : ℝ) ≤ stT449o2 455 := by
  have hc : ((-188793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((455 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11063458593/1250000000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-188793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c456 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((456 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((29837/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1913279/625000 : ℚ) : ℝ) ≤ Real.log ((456 : ℕ)) / 2 := by
    have h := (log_br_456).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((456 : ℕ)) / 2 ≤ ((61224929/20000000 : ℚ) : ℝ) := by
    have h := (log_br_456).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3169529/10000000) (δ := 11379/1000000000) (ψ := -125063/500000) 449 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t456 : ((436565217/31250000000 : ℚ) : ℝ) ≤ stT449o2 456 := by
  have hc : ((3729/12500 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((456 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((436565217/31250000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((3729/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c457 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((457 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((71369/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61246833/20000000 : ℚ) : ℝ) ≤ Real.log ((457 : ℕ)) / 2 := by
    have h := (log_br_457).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((457 : ℕ)) / 2 ≤ ((30623417/10000000 : ℚ) : ℝ) := by
    have h := (log_br_457).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -194011/1000000) (δ := 357/31250000) (ψ := -125063/500000) 449 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t457 : ((417283149/12500000000 : ℚ) : ℝ) ≤ stT449o2 457 := by
  have hc : ((17841/25000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((457 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((417283149/12500000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((17841/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c458 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((458 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((59973/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61268691/20000000 : ℚ) : ℝ) ≤ Real.log ((458 : ℕ)) / 2 := by
    have h := (log_br_458).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((458 : ℕ)) / 2 ≤ ((15317173/5000000 : ℚ) : ℝ) := by
    have h := (log_br_458).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -71333/1000000) (δ := 2831/250000000) (ψ := -125063/500000) 449 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t458 : ((224176508171/5000000000000 : ℚ) : ℝ) ≤ stT449o2 458 := by
  have hc : ((479759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((458 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224176508171/5000000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((479759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c459 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((459 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((489599/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30645251/10000000 : ℚ) : ℝ) ≤ Real.log ((459 : ℕ)) / 2 := by
    have h := (log_br_459).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((459 : ℕ)) / 2 ≤ ((61290503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_459).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 127703/2500000) (δ := 11279/1000000000) (ψ := -125063/500000) 449 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t459 : ((2856419503/62500000000 : ℚ) : ℝ) ≤ stT449o2 459 := by
  have hc : ((244787/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((459 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2856419503/62500000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((244787/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c460 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((460 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((769409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7664033/2500000 : ℚ) : ℝ) ≤ Real.log ((460 : ℕ)) / 2 := by
    have h := (log_br_460).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((460 : ℕ)) / 2 ≤ ((12262453/4000000 : ℚ) : ℝ) := by
    have h := (log_br_460).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 433051/2500000) (δ := 11379/1000000000) (ψ := -125063/500000) 449 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t460 : ((89678793117/2500000000000 : ℚ) : ℝ) ≤ stT449o2 460 := by
  have hc : ((769359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((460 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89678793117/2500000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((769359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c461 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((461 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((380549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3066699/1000000 : ℚ) : ℝ) ≤ Real.log ((461 : ℕ)) / 2 := by
    have h := (log_br_461).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((461 : ℕ)) / 2 ≤ ((61333981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_461).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 590203/2000000) (δ := 5637/500000000) (ψ := -125063/500000) 449 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t461 : ((88607943627/5000000000000 : ℚ) : ℝ) ≤ stT449o2 461 := by
  have hc : ((380499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((461 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88607943627/5000000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((380499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c462 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((462 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-23977/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((479341/156250 : ℚ) : ℝ) ≤ Real.log ((462 : ℕ)) / 2 := by
    have h := (log_br_462).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((462 : ℕ)) / 2 ≤ ((61355649/20000000 : ℚ) : ℝ) := by
    have h := (log_br_462).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4167131/10000000) (δ := 11379/1000000000) (ψ := -125063/500000) 449 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t462 : ((-22321893897/5000000000000 : ℚ) : ℝ) ≤ stT449o2 462 := by
  have hc : ((-47979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((462 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).2
  have h0 : (0:ℝ) ≤ ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22321893897/5000000000000 : ℚ) : ℝ)
      = ((465243/10000000 : ℚ) : ℝ) * ((-47979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c463 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((463 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-549253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6137727/2000000 : ℚ) : ℝ) ≤ Real.log ((463 : ℕ)) / 2 := by
    have h := (log_br_463).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((463 : ℕ)) / 2 ≤ ((61377271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_463).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2690333/5000000) (δ := 11279/1000000000) (ψ := -125063/500000) 449 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t463 : ((-12764153811/500000000000 : ℚ) : ℝ) ≤ stT449o2 463 := by
  have hc : ((-549303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((463 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12764153811/500000000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-549303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c464 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((464 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-87519/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12279769/4000000 : ℚ) : ℝ) ≤ Real.log ((464 : ℕ)) / 2 := by
    have h := (log_br_464).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((464 : ℕ)) / 2 ≤ ((30699423/10000000 : ℚ) : ℝ) := by
    have h := (log_br_464).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6591563/10000000) (δ := 11229/1000000000) (ψ := -125063/500000) 449 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t464 : ((-10158013559/250000000000 : ℚ) : ℝ) ≤ stT449o2 464 := by
  have hc : ((-21881/25000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((464 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).2
  have h0 : (0:ℝ) ≤ ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10158013559/250000000000 : ℚ) : ℝ)
      = ((464239/10000000 : ℚ) : ℝ) * ((-21881/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c465 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((465 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-499883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30710187/10000000 : ℚ) : ℝ) ≤ Real.log ((465 : ℕ)) / 2 := by
    have h := (log_br_465).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((465 : ℕ)) / 2 ≤ ((491363/160000 : ℚ) : ℝ) := by
    have h := (log_br_465).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3899939/5000000) (δ := 11279/1000000000) (ψ := -125063/500000) 449 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t465 : ((-57956709003/1250000000000 : ℚ) : ℝ) ≤ stT449o2 465 := by
  have hc : ((-124977/125000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((465 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).2
  have h0 : (0:ℝ) ≤ ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57956709003/1250000000000 : ℚ) : ℝ)
      = ((463739/10000000 : ℚ) : ℝ) * ((-124977/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c466 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((466 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-895773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((960029/312500 : ℚ) : ℝ) ≤ Real.log ((466 : ℕ)) / 2 := by
    have h := (log_br_466).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((466 : ℕ)) / 2 ≤ ((61441857/20000000 : ℚ) : ℝ) := by
    have h := (log_br_466).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -837801/1250000) (δ := 1409/125000000) (ψ := -125063/500000) 449 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t466 : ((-207491419083/5000000000000 : ℚ) : ℝ) ≤ stT449o2 466 := by
  have hc : ((-895823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((466 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207491419083/5000000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-895823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c467 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((467 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-588279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15365823/5000000 : ℚ) : ℝ) ≤ Real.log ((467 : ℕ)) / 2 := by
    have h := (log_br_467).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((467 : ℕ)) / 2 ≤ ((61463293/20000000 : ℚ) : ℝ) := by
    have h := (log_br_467).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -343707/625000) (δ := 11381/1000000000) (ψ := -125063/500000) 449 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t467 : ((-54449260621/2000000000000 : ℚ) : ℝ) ≤ stT449o2 467 := by
  have hc : ((-588329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((467 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54449260621/2000000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-588329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c468 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((468 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-9261/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30742341/10000000 : ℚ) : ℝ) ≤ Real.log ((468 : ℕ)) / 2 := by
    have h := (log_br_468).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((468 : ℕ)) / 2 ≤ ((61484683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_468).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4298799/10000000) (δ := 2843/250000000) (ψ := -125063/500000) 449 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t468 : ((-34258808363/5000000000000 : ℚ) : ℝ) ≤ stT449o2 468 := by
  have hc : ((-74113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((468 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34258808363/5000000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-74113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c469 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((469 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((324489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61506027/20000000 : ℚ) : ℝ) ≤ Real.log ((469 : ℕ)) / 2 := by
    have h := (log_br_469).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((469 : ℕ)) / 2 ≤ ((15376507/5000000 : ℚ) : ℝ) := by
    have h := (log_br_469).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3100811/10000000) (δ := 5711/500000000) (ψ := -125063/500000) 449 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t469 : ((149811979323/10000000000000 : ℚ) : ℝ) ≤ stT449o2 469 := by
  have hc : ((324439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((469 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).1
  have hw2 : ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((461757/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149811979323/10000000000000 : ℚ) : ℝ)
      = ((461757/10000000 : ℚ) : ℝ) * ((324439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c470 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((470 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((144669/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30763663/10000000 : ℚ) : ℝ) ≤ Real.log ((470 : ℕ)) / 2 := by
    have h := (log_br_470).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((470 : ℕ)) / 2 ≤ ((61527327/20000000 : ℚ) : ℝ) := by
    have h := (log_br_470).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -476351/2500000) (δ := 11281/1000000000) (ψ := -125063/500000) 449 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t470 : ((13345226727/400000000000 : ℚ) : ℝ) ≤ stT449o2 470 := by
  have hc : ((144659/200000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((470 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).1
  have hw2 : ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((92253/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13345226727/400000000000 : ℚ) : ℝ)
      = ((92253/2000000 : ℚ) : ℝ) * ((144659/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c471 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((471 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((959659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3077429/1000000 : ℚ) : ℝ) ≤ Real.log ((471 : ℕ)) / 2 := by
    have h := (log_br_471).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((471 : ℕ)) / 2 ≤ ((61548581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_471).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -712523/10000000) (δ := 11381/1000000000) (ψ := -125063/500000) 449 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t471 : ((17686553479/400000000000 : ℚ) : ℝ) ≤ stT449o2 471 := by
  have hc : ((959609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((471 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).1
  have hw2 : ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18431/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17686553479/400000000000 : ℚ) : ℝ)
      = ((18431/400000 : ℚ) : ℝ) * ((959609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c472 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((472 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((98179/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61569789/20000000 : ℚ) : ℝ) ≤ Real.log ((472 : ℕ)) / 2 := by
    have h := (log_br_472).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((472 : ℕ)) / 2 ≤ ((6156979/2000000 : ℚ) : ℝ) := by
    have h := (log_br_472).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 59729/1250000) (δ := 11331/1000000000) (ψ := -125063/500000) 449 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t472 : ((22594107969/500000000000 : ℚ) : ℝ) ≤ stT449o2 472 := by
  have hc : ((49087/50000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((472 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22594107969/500000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((49087/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c473 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((473 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((98267/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61590953/20000000 : ℚ) : ℝ) ≤ Real.log ((473 : ℕ)) / 2 := by
    have h := (log_br_473).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((473 : ℕ)) / 2 ≤ ((30795477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_473).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1665661/10000000) (δ := 5661/500000000) (ψ := -125063/500000) 449 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t473 : ((903605857/25000000000 : ℚ) : ℝ) ≤ stT449o2 473 := by
  have hc : ((393043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((473 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((903605857/25000000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((393043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c474 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((474 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((417223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61612073/20000000 : ℚ) : ℝ) ≤ Real.log ((474 : ℕ)) / 2 := by
    have h := (log_br_474).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((474 : ℕ)) / 2 ≤ ((30806037/10000000 : ℚ) : ℝ) := by
    have h := (log_br_474).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2851021/10000000) (δ := 5661/500000000) (ψ := -125063/500000) 449 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t474 : ((38322763299/2000000000000 : ℚ) : ℝ) ≤ stT449o2 474 := by
  have hc : ((417173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((474 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38322763299/2000000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((417173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c475 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((475 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-42733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15408287/5000000 : ℚ) : ℝ) ≤ Real.log ((475 : ℕ)) / 2 := by
    have h := (log_br_475).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((475 : ℕ)) / 2 ≤ ((61633149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_475).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 63029/156250) (δ := 11381/1000000000) (ψ := -125063/500000) 449 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t475 : ((-1226888091/625000000000 : ℚ) : ℝ) ≤ stT449o2 475 := by
  have hc : ((-42783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((475 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).2
  have h0 : (0:ℝ) ≤ ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1226888091/625000000000 : ℚ) : ℝ)
      = ((28677/625000 : ℚ) : ℝ) * ((-42783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c476 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((476 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-492421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30827089/10000000 : ℚ) : ℝ) ≤ Real.log ((476 : ℕ)) / 2 := by
    have h := (log_br_476).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((476 : ℕ)) / 2 ≤ ((61654179/20000000 : ℚ) : ℝ) := by
    have h := (log_br_476).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1303541/2500000) (δ := 2843/250000000) (ψ := -125063/500000) 449 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t476 : ((-4514481657/200000000000 : ℚ) : ℝ) ≤ stT449o2 476 := by
  have hc : ((-492471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((476 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4514481657/200000000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-492471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c477 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((477 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-833827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15418791/5000000 : ℚ) : ℝ) ≤ Real.log ((477 : ℕ)) / 2 := by
    have h := (log_br_477).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((477 : ℕ)) / 2 ≤ ((12335033/4000000 : ℚ) : ℝ) := by
    have h := (log_br_477).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1598001/2500000) (δ := 11381/1000000000) (ψ := -125063/500000) 449 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t477 : ((-381806428113/10000000000000 : ℚ) : ℝ) ≤ stT449o2 477 := by
  have hc : ((-833877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((477 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-381806428113/10000000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-833877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c478 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((478 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-496719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61696107/20000000 : ℚ) : ℝ) ≤ Real.log ((478 : ℕ)) / 2 := by
    have h := (log_br_478).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((478 : ℕ)) / 2 ≤ ((15424027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_478).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7567429/10000000) (δ := 5711/500000000) (ψ := -125063/500000) 449 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t478 : ((-2840071727/62500000000 : ℚ) : ℝ) ≤ stT449o2 478 := by
  have hc : ((-62093/62500 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((478 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2840071727/62500000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-62093/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c479 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((479 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-937807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12343401/4000000 : ℚ) : ℝ) ≤ Real.log ((479 : ℕ)) / 2 := by
    have h := (log_br_479).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((479 : ℕ)) / 2 ≤ ((30858503/10000000 : ℚ) : ℝ) := by
    have h := (log_br_479).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3483817/5000000) (δ := 2283/200000000) (ψ := -125063/500000) 449 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t479 : ((-26782382349/625000000000 : ℚ) : ℝ) ≤ stT449o2 479 := by
  have hc : ((-937857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((479 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26782382349/625000000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-937857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c480 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((480 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-680203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61737861/20000000 : ℚ) : ℝ) ≤ Real.log ((480 : ℕ)) / 2 := by
    have h := (log_br_480).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((480 : ℕ)) / 2 ≤ ((30868931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_480).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5797091/10000000) (δ := 2283/200000000) (ψ := -125063/500000) 449 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t480 : ((-77622989577/2500000000000 : ℚ) : ℝ) ≤ stT449o2 480 := by
  have hc : ((-680253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((480 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77622989577/2500000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-680253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c481 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((481 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-69289/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3859917/1250000 : ℚ) : ℝ) ≤ Real.log ((481 : ℕ)) / 2 := by
    have h := (log_br_481).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((481 : ℕ)) / 2 ≤ ((61758673/20000000 : ℚ) : ℝ) := by
    have h := (log_br_481).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4629073/10000000) (δ := 1411/125000000) (ψ := -125063/500000) 449 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t481 : ((-63197562483/5000000000000 : ℚ) : ℝ) ≤ stT449o2 481 := by
  have hc : ((-138603/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((481 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63197562483/5000000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-138603/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c482 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((482 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((18437/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61779441/20000000 : ℚ) : ℝ) ≤ Real.log ((482 : ℕ)) / 2 := by
    have h := (log_br_482).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((482 : ℕ)) / 2 ≤ ((30889721/10000000 : ℚ) : ℝ) := by
    have h := (log_br_482).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3463413/10000000) (δ := 5619/500000000) (ψ := -125063/500000) 449 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t482 : ((4099383/488281250 : ℚ) : ℝ) ≤ stT449o2 482 := by
  have hc : ((576/3125 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((482 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4099383/488281250 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((576/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c483 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((483 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((2423/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30900083/10000000 : ℚ) : ℝ) ≤ Real.log ((483 : ℕ)) / 2 := by
    have h := (log_br_483).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((483 : ℕ)) / 2 ≤ ((61800167/20000000 : ℚ) : ℝ) := by
    have h := (log_br_483).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1150111/5000000) (δ := 2847/250000000) (ψ := -125063/500000) 449 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t483 : ((551205171/20000000000 : ℚ) : ℝ) ≤ stT449o2 483 := by
  have hc : ((6057/10000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((483 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((551205171/20000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((6057/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c484 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((484 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((897929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61820849/20000000 : ℚ) : ℝ) ≤ Real.log ((484 : ℕ)) / 2 := by
    have h := (log_br_484).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((484 : ℕ)) / 2 ≤ ((1236417/400000 : ℚ) : ℝ) := by
    have h := (log_br_484).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1139389/10000000) (δ := 5619/500000000) (ψ := -125063/500000) 449 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t484 : ((81625282011/2000000000000 : ℚ) : ℝ) ≤ stT449o2 484 := by
  have hc : ((897879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((484 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81625282011/2000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((897879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c485 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((485 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((999971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3865093/1250000 : ℚ) : ℝ) ≤ Real.log ((485 : ℕ)) / 2 := by
    have h := (log_br_485).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((485 : ℕ)) / 2 ≤ ((61841489/20000000 : ℚ) : ℝ) := by
    have h := (log_br_485).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 759/400000) (δ := 1411/125000000) (ψ := -125063/500000) 449 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t485 : ((113510031999/2500000000000 : ℚ) : ℝ) ≤ stT449o2 485 := by
  have hc : ((999921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((485 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113510031999/2500000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((999921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c486 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((486 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((891561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30931043/10000000 : ℚ) : ℝ) ≤ Real.log ((486 : ℕ)) / 2 := by
    have h := (log_br_486).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((486 : ℕ)) / 2 ≤ ((61862087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_486).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 587519/5000000) (δ := 2847/250000000) (ψ := -125063/500000) 449 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t486 : ((404397413199/10000000000000 : ℚ) : ℝ) ≤ stT449o2 486 := by
  have hc : ((891511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((486 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((404397413199/10000000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((891511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c487 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((487 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((596651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61882641/20000000 : ℚ) : ℝ) ≤ Real.log ((487 : ℕ)) / 2 := by
    have h := (log_br_487).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((487 : ℕ)) / 2 ≤ ((30941321/10000000 : ℚ) : ℝ) := by
    have h := (log_br_487).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2328687/10000000) (δ := 5619/500000000) (ψ := -125063/500000) 449 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t487 : ((270345566943/10000000000000 : ℚ) : ℝ) ≤ stT449o2 487 := by
  have hc : ((596601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((487 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270345566943/10000000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((596601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c488 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((488 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((177853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30951577/10000000 : ℚ) : ℝ) ≤ Real.log ((488 : ℕ)) / 2 := by
    have h := (log_br_488).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((488 : ℕ)) / 2 ≤ ((12380631/4000000 : ℚ) : ℝ) := by
    have h := (log_br_488).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3479979/10000000) (δ := 2253/200000000) (ψ := -125063/500000) 449 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t488 : ((40243753217/5000000000000 : ℚ) : ℝ) ≤ stT449o2 488 := by
  have hc : ((177803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((488 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40243753217/5000000000000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((177803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c489 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((489 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-277073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7740453/2500000 : ℚ) : ℝ) ≤ Real.log ((489 : ℕ)) / 2 := by
    have h := (log_br_489).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((489 : ℕ)) / 2 ≤ ((495389/160000 : ℚ) : ℝ) := by
    have h := (log_br_489).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2314429/5000000) (δ := 1411/125000000) (ψ := -125063/500000) 449 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t489 : ((-15664931821/1250000000000 : ℚ) : ℝ) ≤ stT449o2 489 := by
  have hc : ((-277123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((489 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15664931821/1250000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-277123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c490 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((490 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-168457/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61944053/20000000 : ℚ) : ℝ) ≤ Real.log ((490 : ℕ)) / 2 := by
    have h := (log_br_490).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((490 : ℕ)) / 2 ≤ ((30972027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_490).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1155087/2000000) (δ := 2283/200000000) (ψ := -125063/500000) 449 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t490 : ((-76106770503/2500000000000 : ℚ) : ℝ) ≤ stT449o2 490 := by
  have hc : ((-336939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((490 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76106770503/2500000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-336939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c491 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((491 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-46549/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61964441/20000000 : ℚ) : ℝ) ≤ Real.log ((491 : ℕ)) / 2 := by
    have h := (log_br_491).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((491 : ℕ)) / 2 ≤ ((30982221/10000000 : ℚ) : ℝ) := by
    have h := (log_br_491).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 216241/312500) (δ := 5619/500000000) (ψ := -125063/500000) 449 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t491 : ((-21008412641/500000000000 : ℚ) : ℝ) ≤ stT449o2 491 := by
  have hc : ((-93103/100000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((491 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21008412641/500000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-93103/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c492 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((492 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-996553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61984787/20000000 : ℚ) : ℝ) ≤ Real.log ((492 : ℕ)) / 2 := by
    have h := (log_br_492).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((492 : ℕ)) / 2 ≤ ((15496197/5000000 : ℚ) : ℝ) := by
    have h := (log_br_492).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1911583/2500000) (δ := 2249/200000000) (ψ := -125063/500000) 449 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t492 : ((-89860702701/2000000000000 : ℚ) : ℝ) ≤ stT449o2 492 := by
  have hc : ((-996603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((492 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).2
  have h0 : (0:ℝ) ≤ ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89860702701/2000000000000 : ℚ) : ℝ)
      = ((90167/2000000 : ℚ) : ℝ) * ((-996603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c493 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((493 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-429141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62005091/20000000 : ℚ) : ℝ) ≤ Real.log ((493 : ℕ)) / 2 := by
    have h := (log_br_493).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((493 : ℕ)) / 2 ≤ ((15501273/5000000 : ℚ) : ℝ) := by
    have h := (log_br_493).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -650677/1000000) (δ := 2249/200000000) (ψ := -125063/500000) 449 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t493 : ((-48321731187/1250000000000 : ℚ) : ℝ) ≤ stT449o2 493 := by
  have hc : ((-214583/250000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((493 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48321731187/1250000000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-214583/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c494 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((494 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-545499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12405071/4000000 : ℚ) : ℝ) ≤ Real.log ((494 : ℕ)) / 2 := by
    have h := (log_br_494).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((494 : ℕ)) / 2 ≤ ((15506339/5000000 : ℚ) : ℝ) := by
    have h := (log_br_494).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5369453/10000000) (δ := 2249/200000000) (ψ := -125063/500000) 449 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t494 : ((-122727248589/5000000000000 : ℚ) : ℝ) ≤ stT449o2 494 := by
  have hc : ((-545549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((494 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122727248589/5000000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-545549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c495 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((495 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((-122691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62045577/20000000 : ℚ) : ℝ) ≤ Real.log ((495 : ℕ)) / 2 := by
    have h := (log_br_495).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((495 : ℕ)) / 2 ≤ ((31022789/10000000 : ℚ) : ℝ) := by
    have h := (log_br_495).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4234493/10000000) (δ := 2269/200000000) (ψ := -125063/500000) 449 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t495 : ((-55168029047/10000000000000 : ℚ) : ℝ) ≤ stT449o2 495 := by
  have hc : ((-122741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((495 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55168029047/10000000000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-122741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c496 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((496 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((324123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62065759/20000000 : ℚ) : ℝ) ≤ Real.log ((496 : ℕ)) / 2 := by
    have h := (log_br_496).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((496 : ℕ)) / 2 ≤ ((387911/125000 : ℚ) : ℝ) := by
    have h := (log_br_496).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3101779/10000000) (δ := 713/62500000) (ψ := -125063/500000) 449 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t496 : ((145512989949/10000000000000 : ℚ) : ℝ) ≤ stT449o2 496 := by
  have hc : ((324073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((496 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145512989949/10000000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((324073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c497 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((497 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((704877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((620859/200000 : ℚ) : ℝ) ≤ Real.log ((497 : ℕ)) / 2 := by
    have h := (log_br_497).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((497 : ℕ)) / 2 ≤ ((62085901/20000000 : ℚ) : ℝ) := by
    have h := (log_br_497).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -394273/2000000) (δ := 5629/500000000) (ψ := -125063/500000) 449 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t497 : ((316157903947/10000000000000 : ℚ) : ℝ) ≤ stT449o2 497 := by
  have hc : ((704827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((497 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316157903947/10000000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((704827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c498 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((498 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((943651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((31053/10000 : ℚ) : ℝ) ≤ Real.log ((498 : ℕ)) / 2 := by
    have h := (log_br_498).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((498 : ℕ)) / 2 ≤ ((62106001/20000000 : ℚ) : ℝ) := by
    have h := (log_br_498).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -210813/2500000) (δ := 2279/200000000) (ψ := -125063/500000) 449 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t498 : ((42283704411/1000000000000 : ℚ) : ℝ) ≤ stT449o2 498 := by
  have hc : ((943601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((498 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).1
  have hw2 : ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((44811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42283704411/1000000000000 : ℚ) : ℝ)
      = ((44811/1000000 : ℚ) : ℝ) * ((943601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c499 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((499 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((993617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3106303/1000000 : ℚ) : ℝ) ≤ Real.log ((499 : ℕ)) / 2 := by
    have h := (log_br_499).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((499 : ℕ)) / 2 ≤ ((62126061/20000000 : ℚ) : ℝ) := by
    have h := (log_br_499).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 56523/2000000) (δ := 5629/500000000) (ψ := -125063/500000) 449 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t499 : ((444781196787/10000000000000 : ℚ) : ℝ) ≤ stT449o2 499 := by
  have hc : ((993567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((499 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).1
  have hw2 : ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((444781196787/10000000000000 : ℚ) : ℝ)
      = ((447661/10000000 : ℚ) : ℝ) * ((993567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_c500 :
    |Real.cos (((449 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((845927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log ((500 : ℕ)) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((500 : ℕ)) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 703119/5000000) (δ := 2279/200000000) (ψ := -125063/500000) 449 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st449o2_t500 : ((378287190801/10000000000000 : ℚ) : ℝ) ≤ stT449o2 500 := by
  have hc : ((845877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((449 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st449o2_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((378287190801/10000000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((845877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st449o2_p1 : ((968831/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT449o2 (i+1) := by
  rw [Finset.sum_range_one]
  exact st449o2_t1

theorem st449o2_p2 : ((24262727297/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 1, stT449o2 (i+1)) + stT449o2 2 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 1
    simpa using h
  have hprev := st449o2_p1
  have hstep := st449o2_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p3 : ((660708752743/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 2, stT449o2 (i+1)) + stT449o2 3 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 2
    simpa using h
  have hprev := st449o2_p2
  have hstep := st449o2_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p4 : ((1520239786453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 3, stT449o2 (i+1)) + stT449o2 4 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 3
    simpa using h
  have hprev := st449o2_p3
  have hstep := st449o2_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p5 : ((447498461827/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 4, stT449o2 (i+1)) + stT449o2 5 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 4
    simpa using h
  have hprev := st449o2_p4
  have hstep := st449o2_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p6 : ((43645918847/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 5, stT449o2 (i+1)) + stT449o2 6 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 5
    simpa using h
  have hprev := st449o2_p5
  have hstep := st449o2_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p7 : ((2143984184521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 6, stT449o2 (i+1)) + stT449o2 7 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 6
    simpa using h
  have hprev := st449o2_p6
  have hstep := st449o2_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p8 : ((271042119089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 7, stT449o2 (i+1)) + stT449o2 8 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 7
    simpa using h
  have hprev := st449o2_p7
  have hstep := st449o2_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p9 : ((-116661140737/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 8, stT449o2 (i+1)) + stT449o2 9 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 8
    simpa using h
  have hprev := st449o2_p8
  have hstep := st449o2_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p10 : ((-822898858633/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 9, stT449o2 (i+1)) + stT449o2 10 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 9
    simpa using h
  have hprev := st449o2_p9
  have hstep := st449o2_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p11 : ((-4729987604669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 10, stT449o2 (i+1)) + stT449o2 11 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 10
    simpa using h
  have hprev := st449o2_p10
  have hstep := st449o2_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p12 : ((-3399720782351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 11, stT449o2 (i+1)) + stT449o2 12 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 11
    simpa using h
  have hprev := st449o2_p11
  have hstep := st449o2_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p13 : ((-4482456743737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 12, stT449o2 (i+1)) + stT449o2 13 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 12
    simpa using h
  have hprev := st449o2_p12
  have hstep := st449o2_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p14 : ((-5829731647489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 13, stT449o2 (i+1)) + stT449o2 14 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 13
    simpa using h
  have hprev := st449o2_p13
  have hstep := st449o2_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p15 : ((-5044099830777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 14, stT449o2 (i+1)) + stT449o2 15 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 14
    simpa using h
  have hprev := st449o2_p14
  have hstep := st449o2_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p16 : ((-3070709830777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 15, stT449o2 (i+1)) + stT449o2 16 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 15
    simpa using h
  have hprev := st449o2_p15
  have hstep := st449o2_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p17 : ((-3394883047397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 16, stT449o2 (i+1)) + stT449o2 17 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 16
    simpa using h
  have hprev := st449o2_p16
  have hstep := st449o2_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p18 : ((-1078054974959/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 17, stT449o2 (i+1)) + stT449o2 18 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 17
    simpa using h
  have hprev := st449o2_p17
  have hstep := st449o2_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p19 : ((-4246769894783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 18, stT449o2 (i+1)) + stT449o2 19 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 18
    simpa using h
  have hprev := st449o2_p18
  have hstep := st449o2_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p20 : ((-1137589095671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 19, stT449o2 (i+1)) + stT449o2 20 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 19
    simpa using h
  have hprev := st449o2_p19
  have hstep := st449o2_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p21 : ((-166006752567/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 20, stT449o2 (i+1)) + stT449o2 21 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 20
    simpa using h
  have hprev := st449o2_p20
  have hstep := st449o2_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p22 : ((-107778421459/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 21, stT449o2 (i+1)) + stT449o2 22 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 21
    simpa using h
  have hprev := st449o2_p21
  have hstep := st449o2_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p23 : ((-196639503679/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 22, stT449o2 (i+1)) + stT449o2 23 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 22
    simpa using h
  have hprev := st449o2_p22
  have hstep := st449o2_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p24 : ((-327875539097/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 23, stT449o2 (i+1)) + stT449o2 24 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 23
    simpa using h
  have hprev := st449o2_p23
  have hstep := st449o2_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p25 : ((-138129539097/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 24, stT449o2 (i+1)) + stT449o2 25 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 24
    simpa using h
  have hprev := st449o2_p24
  have hstep := st449o2_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p26 : ((-406994062039/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 25, stT449o2 (i+1)) + stT449o2 26 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 25
    simpa using h
  have hprev := st449o2_p25
  have hstep := st449o2_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p27 : ((-662470795703/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 26, stT449o2 (i+1)) + stT449o2 27 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 26
    simpa using h
  have hprev := st449o2_p26
  have hstep := st449o2_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p28 : ((-140507474779/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 27, stT449o2 (i+1)) + stT449o2 28 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 27
    simpa using h
  have hprev := st449o2_p27
  have hstep := st449o2_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p29 : ((-563837400051/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 28, stT449o2 (i+1)) + stT449o2 29 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 28
    simpa using h
  have hprev := st449o2_p28
  have hstep := st449o2_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p30 : ((-1964234348857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 29, stT449o2 (i+1)) + stT449o2 30 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 29
    simpa using h
  have hprev := st449o2_p29
  have hstep := st449o2_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p31 : ((-1018350318811/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 30, stT449o2 (i+1)) + stT449o2 31 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 30
    simpa using h
  have hprev := st449o2_p30
  have hstep := st449o2_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p32 : ((-1425475213813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 31, stT449o2 (i+1)) + stT449o2 32 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 31
    simpa using h
  have hprev := st449o2_p31
  have hstep := st449o2_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p33 : ((-569520858017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 32, stT449o2 (i+1)) + stT449o2 33 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 32
    simpa using h
  have hprev := st449o2_p32
  have hstep := st449o2_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p34 : ((132007508259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 33, stT449o2 (i+1)) + stT449o2 34 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 33
    simpa using h
  have hprev := st449o2_p33
  have hstep := st449o2_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p35 : ((510406618371/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 34, stT449o2 (i+1)) + stT449o2 35 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 34
    simpa using h
  have hprev := st449o2_p34
  have hstep := st449o2_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p36 : ((437781152821/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 35, stT449o2 (i+1)) + stT449o2 36 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 35
    simpa using h
  have hprev := st449o2_p35
  have hstep := st449o2_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p37 : ((62934039509/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 36, stT449o2 (i+1)) + stT449o2 37 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 36
    simpa using h
  have hprev := st449o2_p36
  have hstep := st449o2_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p38 : ((831550181297/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 37, stT449o2 (i+1)) + stT449o2 38 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 37
    simpa using h
  have hprev := st449o2_p37
  have hstep := st449o2_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p39 : ((8140819361653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 38, stT449o2 (i+1)) + stT449o2 39 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 38
    simpa using h
  have hprev := st449o2_p38
  have hstep := st449o2_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p40 : ((9025538805001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 39, stT449o2 (i+1)) + stT449o2 40 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 39
    simpa using h
  have hprev := st449o2_p39
  have hstep := st449o2_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p41 : ((1759713659597/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 40, stT449o2 (i+1)) + stT449o2 41 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 40
    simpa using h
  have hprev := st449o2_p40
  have hstep := st449o2_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p42 : ((7484409445137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 41, stT449o2 (i+1)) + stT449o2 42 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 41
    simpa using h
  have hprev := st449o2_p41
  have hstep := st449o2_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p43 : ((6110410784011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 42, stT449o2 (i+1)) + stT449o2 43 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 42
    simpa using h
  have hprev := st449o2_p42
  have hstep := st449o2_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p44 : ((6110501237371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 43, stT449o2 (i+1)) + stT449o2 44 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 43
    simpa using h
  have hprev := st449o2_p43
  have hstep := st449o2_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p45 : ((7519419906223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 44, stT449o2 (i+1)) + stT449o2 45 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 44
    simpa using h
  have hprev := st449o2_p44
  have hstep := st449o2_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p46 : ((8295677919019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 45, stT449o2 (i+1)) + stT449o2 46 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 45
    simpa using h
  have hprev := st449o2_p45
  have hstep := st449o2_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p47 : ((7152549959169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 46, stT449o2 (i+1)) + stT449o2 47 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 46
    simpa using h
  have hprev := st449o2_p46
  have hstep := st449o2_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p48 : ((6239971153041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 47, stT449o2 (i+1)) + stT449o2 48 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 47
    simpa using h
  have hprev := st449o2_p47
  have hstep := st449o2_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p49 : ((7418130799593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 48, stT449o2 (i+1)) + stT449o2 49 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 48
    simpa using h
  have hprev := st449o2_p48
  have hstep := st449o2_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p50 : ((8000079449093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 49, stT449o2 (i+1)) + stT449o2 50 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 49
    simpa using h
  have hprev := st449o2_p49
  have hstep := st449o2_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p51 : ((1654262127683/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 50, stT449o2 (i+1)) + stT449o2 51 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 50
    simpa using h
  have hprev := st449o2_p50
  have hstep := st449o2_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p52 : ((860808634279/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 51, stT449o2 (i+1)) + stT449o2 52 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 51
    simpa using h
  have hprev := st449o2_p51
  have hstep := st449o2_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p53 : ((7994977924467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 52, stT449o2 (i+1)) + stT449o2 53 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 52
    simpa using h
  have hprev := st449o2_p52
  have hstep := st449o2_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p54 : ((1350820293871/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 53, stT449o2 (i+1)) + stT449o2 54 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 53
    simpa using h
  have hprev := st449o2_p53
  have hstep := st449o2_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p55 : ((872749466593/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 54, stT449o2 (i+1)) + stT449o2 55 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 54
    simpa using h
  have hprev := st449o2_p54
  have hstep := st449o2_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p56 : ((984591597263/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 55, stT449o2 (i+1)) + stT449o2 56 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 55
    simpa using h
  have hprev := st449o2_p55
  have hstep := st449o2_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p57 : ((6552150770383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 56, stT449o2 (i+1)) + stT449o2 57 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 56
    simpa using h
  have hprev := st449o2_p56
  have hstep := st449o2_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p58 : ((7505900059039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 57, stT449o2 (i+1)) + stT449o2 58 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 57
    simpa using h
  have hprev := st449o2_p57
  have hstep := st449o2_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p59 : ((7353893986419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 58, stT449o2 (i+1)) + stT449o2 59 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 58
    simpa using h
  have hprev := st449o2_p58
  have hstep := st449o2_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p60 : ((6718388787719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 59, stT449o2 (i+1)) + stT449o2 60 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 59
    simpa using h
  have hprev := st449o2_p59
  have hstep := st449o2_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p61 : ((7849876877047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 60, stT449o2 (i+1)) + stT449o2 61 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 60
    simpa using h
  have hprev := st449o2_p60
  have hstep := st449o2_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p62 : ((6580117447429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 61, stT449o2 (i+1)) + stT449o2 62 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 61
    simpa using h
  have hprev := st449o2_p61
  have hstep := st449o2_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p63 : ((3850960894617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 62, stT449o2 (i+1)) + stT449o2 63 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 62
    simpa using h
  have hprev := st449o2_p62
  have hstep := st449o2_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p64 : ((3446173070787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 63, stT449o2 (i+1)) + stT449o2 64 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 63
    simpa using h
  have hprev := st449o2_p63
  have hstep := st449o2_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p65 : ((3667711448457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 64, stT449o2 (i+1)) + stT449o2 65 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 64
    simpa using h
  have hprev := st449o2_p64
  have hstep := st449o2_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p66 : ((7237751022579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 65, stT449o2 (i+1)) + stT449o2 66 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 65
    simpa using h
  have hprev := st449o2_p65
  have hstep := st449o2_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p67 : ((3524522173897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 66, stT449o2 (i+1)) + stT449o2 67 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 66
    simpa using h
  have hprev := st449o2_p66
  have hstep := st449o2_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p68 : ((3726372426997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 67, stT449o2 (i+1)) + stT449o2 68 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 67
    simpa using h
  have hprev := st449o2_p67
  have hstep := st449o2_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p69 : ((3450912633771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 68, stT449o2 (i+1)) + stT449o2 69 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 68
    simpa using h
  have hprev := st449o2_p68
  have hstep := st449o2_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p70 : ((3770319388351/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 69, stT449o2 (i+1)) + stT449o2 70 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 69
    simpa using h
  have hprev := st449o2_p69
  have hstep := st449o2_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p71 : ((1715959294349/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 70, stT449o2 (i+1)) + stT449o2 71 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 70
    simpa using h
  have hprev := st449o2_p70
  have hstep := st449o2_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p72 : ((941773547041/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 71, stT449o2 (i+1)) + stT449o2 72 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 71
    simpa using h
  have hprev := st449o2_p71
  have hstep := st449o2_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p73 : ((1728075123459/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 72, stT449o2 (i+1)) + stT449o2 73 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 72
    simpa using h
  have hprev := st449o2_p72
  have hstep := st449o2_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p74 : ((93022589367/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 73, stT449o2 (i+1)) + stT449o2 74 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 73
    simpa using h
  have hprev := st449o2_p73
  have hstep := st449o2_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p75 : ((881420146503/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 74, stT449o2 (i+1)) + stT449o2 75 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 74
    simpa using h
  have hprev := st449o2_p74
  have hstep := st449o2_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p76 : ((145061886773/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 75, stT449o2 (i+1)) + stT449o2 76 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 75
    simpa using h
  have hprev := st449o2_p75
  have hstep := st449o2_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p77 : ((291491983309/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 76, stT449o2 (i+1)) + stT449o2 77 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 76
    simpa using h
  have hprev := st449o2_p76
  have hstep := st449o2_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p78 : ((6979941587347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 77, stT449o2 (i+1)) + stT449o2 78 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 77
    simpa using h
  have hprev := st449o2_p77
  have hstep := st449o2_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p79 : ((7574210290573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 78, stT449o2 (i+1)) + stT449o2 79 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 78
    simpa using h
  have hprev := st449o2_p78
  have hstep := st449o2_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p80 : ((6716596596091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 79, stT449o2 (i+1)) + stT449o2 80 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 79
    simpa using h
  have hprev := st449o2_p79
  have hstep := st449o2_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p81 : ((7762605380379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 80, stT449o2 (i+1)) + stT449o2 81 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 80
    simpa using h
  have hprev := st449o2_p80
  have hstep := st449o2_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p82 : ((6659258969827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 81, stT449o2 (i+1)) + stT449o2 82 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 81
    simpa using h
  have hprev := st449o2_p81
  have hstep := st449o2_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p83 : ((7641073395419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 82, stT449o2 (i+1)) + stT449o2 83 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 82
    simpa using h
  have hprev := st449o2_p82
  have hstep := st449o2_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p84 : ((6976871266829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 83, stT449o2 (i+1)) + stT449o2 84 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 83
    simpa using h
  have hprev := st449o2_p83
  have hstep := st449o2_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p85 : ((7159961609081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 84, stT449o2 (i+1)) + stT449o2 85 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 84
    simpa using h
  have hprev := st449o2_p84
  have hstep := st449o2_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p86 : ((7525788357139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 85, stT449o2 (i+1)) + stT449o2 86 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 85
    simpa using h
  have hprev := st449o2_p85
  have hstep := st449o2_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p87 : ((3345522195839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 86, stT449o2 (i+1)) + stT449o2 87 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 86
    simpa using h
  have hprev := st449o2_p86
  have hstep := st449o2_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p88 : ((7751387981751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 87, stT449o2 (i+1)) + stT449o2 88 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 87
    simpa using h
  have hprev := st449o2_p87
  have hstep := st449o2_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p89 : ((6822247794849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 88, stT449o2 (i+1)) + stT449o2 89 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 88
    simpa using h
  have hprev := st449o2_p88
  have hstep := st449o2_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p90 : ((7266739417593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 89, stT449o2 (i+1)) + stT449o2 90 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 89
    simpa using h
  have hprev := st449o2_p89
  have hstep := st449o2_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p91 : ((7501125237153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 90, stT449o2 (i+1)) + stT449o2 91 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 90
    simpa using h
  have hprev := st449o2_p90
  have hstep := st449o2_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p92 : ((3337839766353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 91, stT449o2 (i+1)) + stT449o2 92 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 91
    simpa using h
  have hprev := st449o2_p91
  have hstep := st449o2_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p93 : ((3855438005807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 92, stT449o2 (i+1)) + stT449o2 93 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 92
    simpa using h
  have hprev := st449o2_p92
  have hstep := st449o2_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p94 : ((699061133773/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 93, stT449o2 (i+1)) + stT449o2 94 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 93
    simpa using h
  have hprev := st449o2_p93
  have hstep := st449o2_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p95 : ((699781370329/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 94, stT449o2 (i+1)) + stT449o2 95 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 94
    simpa using h
  have hprev := st449o2_p94
  have hstep := st449o2_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p96 : ((771823466021/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 95, stT449o2 (i+1)) + stT449o2 96 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 95
    simpa using h
  have hprev := st449o2_p95
  have hstep := st449o2_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p97 : ((3351618469789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 96, stT449o2 (i+1)) + stT449o2 97 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 96
    simpa using h
  have hprev := st449o2_p96
  have hstep := st449o2_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p98 : ((3678408702701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 97, stT449o2 (i+1)) + stT449o2 98 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 97
    simpa using h
  have hprev := st449o2_p97
  have hstep := st449o2_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p99 : ((3757776474591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 98, stT449o2 (i+1)) + stT449o2 99 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 98
    simpa using h
  have hprev := st449o2_p98
  have hstep := st449o2_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p100 : ((3325551474591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 99, stT449o2 (i+1)) + stT449o2 100 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 99
    simpa using h
  have hprev := st449o2_p99
  have hstep := st449o2_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p101 : ((7574780870727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 100, stT449o2 (i+1)) + stT449o2 101 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 100
    simpa using h
  have hprev := st449o2_p100
  have hstep := st449o2_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p102 : ((1464006326539/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 101, stT449o2 (i+1)) + stT449o2 102 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 101
    simpa using h
  have hprev := st449o2_p101
  have hstep := st449o2_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p103 : ((53535038531/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 102, stT449o2 (i+1)) + stT449o2 103 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 102
    simpa using h
  have hprev := st449o2_p102
  have hstep := st449o2_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p104 : ((1533636701399/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 103, stT449o2 (i+1)) + stT449o2 104 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 103
    simpa using h
  have hprev := st449o2_p103
  have hstep := st449o2_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p105 : ((7213448773431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 104, stT449o2 (i+1)) + stT449o2 105 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 104
    simpa using h
  have hprev := st449o2_p104
  have hstep := st449o2_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p106 : ((6723257241093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 105, stT449o2 (i+1)) + stT449o2 106 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 105
    simpa using h
  have hprev := st449o2_p105
  have hstep := st449o2_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p107 : ((7689912035269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 106, stT449o2 (i+1)) + stT449o2 107 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 106
    simpa using h
  have hprev := st449o2_p106
  have hstep := st449o2_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p108 : ((3603432460011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 107, stT449o2 (i+1)) + stT449o2 108 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 107
    simpa using h
  have hprev := st449o2_p107
  have hstep := st449o2_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p109 : ((838617319259/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 108, stT449o2 (i+1)) + stT449o2 109 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 108
    simpa using h
  have hprev := st449o2_p108
  have hstep := st449o2_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p110 : ((3830101412081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 109, stT449o2 (i+1)) + stT449o2 110 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 109
    simpa using h
  have hprev := st449o2_p109
  have hstep := st449o2_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p111 : ((729601659451/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 110, stT449o2 (i+1)) + stT449o2 111 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 110
    simpa using h
  have hprev := st449o2_p110
  have hstep := st449o2_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p112 : ((3331371120791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 111, stT449o2 (i+1)) + stT449o2 112 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 111
    simpa using h
  have hprev := st449o2_p111
  have hstep := st449o2_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p113 : ((3779341984791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 112, stT449o2 (i+1)) + stT449o2 113 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 112
    simpa using h
  have hprev := st449o2_p112
  have hstep := st449o2_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p114 : ((3733702149011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 113, stT449o2 (i+1)) + stT449o2 114 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 113
    simpa using h
  have hprev := st449o2_p113
  have hstep := st449o2_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p115 : ((3321738225101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 114, stT449o2 (i+1)) + stT449o2 115 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 114
    simpa using h
  have hprev := st449o2_p114
  have hstep := st449o2_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p116 : ((3673658019143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 115, stT449o2 (i+1)) + stT449o2 116 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 115
    simpa using h
  have hprev := st449o2_p115
  have hstep := st449o2_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p117 : ((3833927490143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 116, stT449o2 (i+1)) + stT449o2 117 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 116
    simpa using h
  have hprev := st449o2_p116
  have hstep := st449o2_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p118 : ((3373663925093/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 117, stT449o2 (i+1)) + stT449o2 118 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 117
    simpa using h
  have hprev := st449o2_p117
  have hstep := st449o2_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p119 : ((3513223862009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 118, stT449o2 (i+1)) + stT449o2 119 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 118
    simpa using h
  have hprev := st449o2_p118
  have hstep := st449o2_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p120 : ((242836789829/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 119, stT449o2 (i+1)) + stT449o2 120 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 119
    simpa using h
  have hprev := st449o2_p119
  have hstep := st449o2_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p121 : ((7053212657317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 120, stT449o2 (i+1)) + stT449o2 121 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 120
    simpa using h
  have hprev := st449o2_p120
  have hstep := st449o2_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p122 : ((6713802091339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 121, stT449o2 (i+1)) + stT449o2 122 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 121
    simpa using h
  have hprev := st449o2_p121
  have hstep := st449o2_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p123 : ((951085528597/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 122, stT449o2 (i+1)) + stT449o2 123 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 122
    simpa using h
  have hprev := st449o2_p122
  have hstep := st449o2_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p124 : ((468561053387/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 123, stT449o2 (i+1)) + stT449o2 124 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 123
    simpa using h
  have hprev := st449o2_p123
  have hstep := st449o2_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p125 : ((1664732280793/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 124, stT449o2 (i+1)) + stT449o2 125 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 124
    simpa using h
  have hprev := st449o2_p124
  have hstep := st449o2_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p126 : ((3571746012221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 125, stT449o2 (i+1)) + stT449o2 126 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 125
    simpa using h
  have hprev := st449o2_p125
  have hstep := st449o2_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p127 : ((3887433557493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 126, stT449o2 (i+1)) + stT449o2 127 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 126
    simpa using h
  have hprev := st449o2_p126
  have hstep := st449o2_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p128 : ((3523094362983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 127, stT449o2 (i+1)) + stT449o2 128 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 127
    simpa using h
  have hprev := st449o2_p127
  have hstep := st449o2_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p129 : ((6682774651657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 128, stT449o2 (i+1)) + stT449o2 129 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 128
    simpa using h
  have hprev := st449o2_p128
  have hstep := st449o2_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p130 : ((7529714479937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 129, stT449o2 (i+1)) + stT449o2 130 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 129
    simpa using h
  have hprev := st449o2_p129
  have hstep := st449o2_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p131 : ((7628284017809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 130, stT449o2 (i+1)) + stT449o2 131 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 130
    simpa using h
  have hprev := st449o2_p130
  have hstep := st449o2_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p132 : ((6758088244167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 131, stT449o2 (i+1)) + stT449o2 132 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 131
    simpa using h
  have hprev := st449o2_p131
  have hstep := st449o2_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p133 : ((6884946290867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 132, stT449o2 (i+1)) + stT449o2 133 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 132
    simpa using h
  have hprev := st449o2_p132
  have hstep := st449o2_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p134 : ((7720237537427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 133, stT449o2 (i+1)) + stT449o2 134 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 133
    simpa using h
  have hprev := st449o2_p133
  have hstep := st449o2_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p135 : ((3710081539581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 134, stT449o2 (i+1)) + stT449o2 135 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 134
    simpa using h
  have hprev := st449o2_p134
  have hstep := st449o2_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p136 : ((6645077728941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 135, stT449o2 (i+1)) + stT449o2 136 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 135
    simpa using h
  have hprev := st449o2_p135
  have hstep := st449o2_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p137 : ((1413320418863/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 136, stT449o2 (i+1)) + stT449o2 137 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 136
    simpa using h
  have hprev := st449o2_p136
  have hstep := st449o2_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p138 : ((7779555383251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 137, stT449o2 (i+1)) + stT449o2 138 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 137
    simpa using h
  have hprev := st449o2_p137
  have hstep := st449o2_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p139 : ((7281098457243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 138, stT449o2 (i+1)) + stT449o2 139 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 138
    simpa using h
  have hprev := st449o2_p138
  have hstep := st449o2_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p140 : ((6616850575303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 139, stT449o2 (i+1)) + stT449o2 140 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 139
    simpa using h
  have hprev := st449o2_p139
  have hstep := st449o2_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p141 : ((447204620131/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 140, stT449o2 (i+1)) + stT449o2 141 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 140
    simpa using h
  have hprev := st449o2_p140
  have hstep := st449o2_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p142 : ((3895954258787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 141, stT449o2 (i+1)) + stT449o2 142 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 141
    simpa using h
  have hprev := st449o2_p141
  have hstep := st449o2_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p143 : ((724414593777/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 142, stT449o2 (i+1)) + stT449o2 143 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 142
    simpa using h
  have hprev := st449o2_p142
  have hstep := st449o2_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p144 : ((3305473548939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 143, stT449o2 (i+1)) + stT449o2 144 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 143
    simpa using h
  have hprev := st449o2_p143
  have hstep := st449o2_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p145 : ((446246591589/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 144, stT449o2 (i+1)) + stT449o2 145 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 144
    simpa using h
  have hprev := st449o2_p144
  have hstep := st449o2_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p146 : ((7792264554029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 145, stT449o2 (i+1)) + stT449o2 146 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 145
    simpa using h
  have hprev := st449o2_p145
  have hstep := st449o2_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p147 : ((3569340391/4882812500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 146, stT449o2 (i+1)) + stT449o2 147 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 146
    simpa using h
  have hprev := st449o2_p146
  have hstep := st449o2_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p148 : ((3310234375539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 147, stT449o2 (i+1)) + stT449o2 148 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 147
    simpa using h
  have hprev := st449o2_p147
  have hstep := st449o2_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p149 : ((7025145107379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 148, stT449o2 (i+1)) + stT449o2 149 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 148
    simpa using h
  have hprev := st449o2_p148
  have hstep := st449o2_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p150 : ((7761177059571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 149, stT449o2 (i+1)) + stT449o2 150 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 149
    simpa using h
  have hprev := st449o2_p149
  have hstep := st449o2_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p151 : ((1493601263433/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 150, stT449o2 (i+1)) + stT449o2 151 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 150
    simpa using h
  have hprev := st449o2_p150
  have hstep := st449o2_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p152 : ((6688344163217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 151, stT449o2 (i+1)) + stT449o2 152 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 151
    simpa using h
  have hprev := st449o2_p151
  have hstep := st449o2_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p153 : ((6833745872321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 152, stT449o2 (i+1)) + stT449o2 153 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 152
    simpa using h
  have hprev := st449o2_p152
  have hstep := st449o2_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p154 : ((7637402628607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 153, stT449o2 (i+1)) + stT449o2 154 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 153
    simpa using h
  have hprev := st449o2_p153
  have hstep := st449o2_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p155 : ((7673558728673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 154, stT449o2 (i+1)) + stT449o2 155 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 154
    simpa using h
  have hprev := st449o2_p154
  have hstep := st449o2_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p156 : ((3442355184981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 155, stT449o2 (i+1)) + stT449o2 156 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 155
    simpa using h
  have hprev := st449o2_p155
  have hstep := st449o2_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p157 : ((3321202386033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 156, stT449o2 (i+1)) + stT449o2 157 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 156
    simpa using h
  have hprev := st449o2_p156
  have hstep := st449o2_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p158 : ((229918516639/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 157, stT449o2 (i+1)) + stT449o2 158 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 157
    simpa using h
  have hprev := st449o2_p157
  have hstep := st449o2_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p159 : ((1562099968429/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 158, stT449o2 (i+1)) + stT449o2 159 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 158
    simpa using h
  have hprev := st449o2_p158
  have hstep := st449o2_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p160 : ((289748628059/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 159, stT449o2 (i+1)) + stT449o2 160 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 159
    simpa using h
  have hprev := st449o2_p159
  have hstep := st449o2_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p161 : ((3302797811331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 160, stT449o2 (i+1)) + stT449o2 161 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 160
    simpa using h
  have hprev := st449o2_p160
  have hstep := st449o2_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p162 : ((1736218502939/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 161, stT449o2 (i+1)) + stT449o2 162 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 161
    simpa using h
  have hprev := st449o2_p161
  have hstep := st449o2_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p163 : ((481394027921/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 162, stT449o2 (i+1)) + stT449o2 163 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 162
    simpa using h
  have hprev := st449o2_p162
  have hstep := st449o2_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p164 : ((1913934135763/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 163, stT449o2 (i+1)) + stT449o2 164 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 163
    simpa using h
  have hprev := st449o2_p163
  have hstep := st449o2_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p165 : ((6885530892899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 164, stT449o2 (i+1)) + stT449o2 165 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 164
    simpa using h
  have hprev := st449o2_p164
  have hstep := st449o2_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p166 : ((6611537171483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 165, stT449o2 (i+1)) + stT449o2 166 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 165
    simpa using h
  have hprev := st449o2_p165
  have hstep := st449o2_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p167 : ((3628713168181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 166, stT449o2 (i+1)) + stT449o2 167 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 166
    simpa using h
  have hprev := st449o2_p166
  have hstep := st449o2_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p168 : ((3909068966809/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 167, stT449o2 (i+1)) + stT449o2 168 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 167
    simpa using h
  have hprev := st449o2_p167
  have hstep := st449o2_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p169 : ((7436760126897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 168, stT449o2 (i+1)) + stT449o2 169 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 168
    simpa using h
  have hprev := st449o2_p168
  have hstep := st449o2_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p170 : ((1674507735843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 169, stT449o2 (i+1)) + stT449o2 170 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 169
    simpa using h
  have hprev := st449o2_p169
  have hstep := st449o2_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p171 : ((671198094737/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 170, stT449o2 (i+1)) + stT449o2 171 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 170
    simpa using h
  have hprev := st449o2_p170
  have hstep := st449o2_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p172 : ((3725973704353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 171, stT449o2 (i+1)) + stT449o2 172 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 171
    simpa using h
  have hprev := st449o2_p171
  have hstep := st449o2_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p173 : ((7824928784291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 172, stT449o2 (i+1)) + stT449o2 173 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 172
    simpa using h
  have hprev := st449o2_p172
  have hstep := st449o2_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p174 : ((911390403591/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 173, stT449o2 (i+1)) + stT449o2 174 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 173
    simpa using h
  have hprev := st449o2_p173
  have hstep := st449o2_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p175 : ((6626568658461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 174, stT449o2 (i+1)) + stT449o2 175 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 174
    simpa using h
  have hprev := st449o2_p174
  have hstep := st449o2_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p176 : ((1356037421461/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 175, stT449o2 (i+1)) + stT449o2 176 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 175
    simpa using h
  have hprev := st449o2_p175
  have hstep := st449o2_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p177 : ((7528510080339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 176, stT449o2 (i+1)) + stT449o2 177 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 176
    simpa using h
  have hprev := st449o2_p176
  have hstep := st449o2_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p178 : ((3910019706629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 177, stT449o2 (i+1)) + stT449o2 178 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 177
    simpa using h
  have hprev := st449o2_p177
  have hstep := st449o2_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p179 : ((725445608693/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 178, stT449o2 (i+1)) + stT449o2 179 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 178
    simpa using h
  have hprev := st449o2_p178
  have hstep := st449o2_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p180 : ((3307190065609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 179, stT449o2 (i+1)) + stT449o2 180 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 179
    simpa using h
  have hprev := st449o2_p179
  have hstep := st449o2_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p181 : ((3385024096819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 180, stT449o2 (i+1)) + stT449o2 181 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 180
    simpa using h
  have hprev := st449o2_p180
  have hstep := st449o2_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p182 : ((1876418519681/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 181, stT449o2 (i+1)) + stT449o2 182 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 181
    simpa using h
  have hprev := st449o2_p181
  have hstep := st449o2_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p183 : ((7836127303133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 182, stT449o2 (i+1)) + stT449o2 183 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 182
    simpa using h
  have hprev := st449o2_p182
  have hstep := st449o2_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p184 : ((7328243429463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 183, stT449o2 (i+1)) + stT449o2 184 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 183
    simpa using h
  have hprev := st449o2_p183
  have hstep := st449o2_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p185 : ((6652745532623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 184, stT449o2 (i+1)) + stT449o2 185 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 184
    simpa using h
  have hprev := st449o2_p184
  have hstep := st449o2_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p186 : ((1671495218867/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 185, stT449o2 (i+1)) + stT449o2 186 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 185
    simpa using h
  have hprev := st449o2_p185
  have hstep := st449o2_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p187 : ((1844929170927/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 186, stT449o2 (i+1)) + stT449o2 187 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 186
    simpa using h
  have hprev := st449o2_p186
  have hstep := st449o2_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p188 : ((1961696860623/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 187, stT449o2 (i+1)) + stT449o2 188 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 187
    simpa using h
  have hprev := st449o2_p187
  have hstep := st449o2_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p189 : ((7500646572547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 188, stT449o2 (i+1)) + stT449o2 189 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 188
    simpa using h
  have hprev := st449o2_p188
  have hstep := st449o2_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p190 : ((6779500670237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 189, stT449o2 (i+1)) + stT449o2 190 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 189
    simpa using h
  have hprev := st449o2_p189
  have hstep := st449o2_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p191 : ((6577744805837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 190, stT449o2 (i+1)) + stT449o2 191 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 190
    simpa using h
  have hprev := st449o2_p190
  have hstep := st449o2_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p192 : ((7138416219267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 191, stT449o2 (i+1)) + stT449o2 192 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 191
    simpa using h
  have hprev := st449o2_p191
  have hstep := st449o2_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p193 : ((1943776565813/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 192, stT449o2 (i+1)) + stT449o2 193 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 192
    simpa using h
  have hprev := st449o2_p192
  have hstep := st449o2_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p194 : ((7721527136959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 193, stT449o2 (i+1)) + stT449o2 194 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 193
    simpa using h
  have hprev := st449o2_p193
  have hstep := st449o2_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p195 : ((7046826499639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 194, stT449o2 (i+1)) + stT449o2 195 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 194
    simpa using h
  have hprev := st449o2_p194
  have hstep := st449o2_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p196 : ((6552450587603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 195, stT449o2 (i+1)) + stT449o2 196 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 195
    simpa using h
  have hprev := st449o2_p195
  have hstep := st449o2_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p197 : ((6815454613283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 196, stT449o2 (i+1)) + stT449o2 197 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 196
    simpa using h
  have hprev := st449o2_p196
  have hstep := st449o2_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p198 : ((7524976593517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 197, stT449o2 (i+1)) + stT449o2 198 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 197
    simpa using h
  have hprev := st449o2_p197
  have hstep := st449o2_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p199 : ((7862153005643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 198, stT449o2 (i+1)) + stT449o2 199 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 198
    simpa using h
  have hprev := st449o2_p198
  have hstep := st449o2_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p200 : ((7445785776619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 199, stT449o2 (i+1)) + stT449o2 200 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 199
    simpa using h
  have hprev := st449o2_p199
  have hstep := st449o2_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p201 : ((6751608225183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 200, stT449o2 (i+1)) + stT449o2 201 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 200
    simpa using h
  have hprev := st449o2_p200
  have hstep := st449o2_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p202 : ((6558348148131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 201, stT449o2 (i+1)) + stT449o2 202 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 201
    simpa using h
  have hprev := st449o2_p201
  have hstep := st449o2_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p203 : ((7076452148601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 202, stT449o2 (i+1)) + stT449o2 203 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 202
    simpa using h
  have hprev := st449o2_p202
  have hstep := st449o2_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p204 : ((7730971026201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 203, stT449o2 (i+1)) + stT449o2 204 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 203
    simpa using h
  have hprev := st449o2_p203
  have hstep := st449o2_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p205 : ((7807708927161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 204, stT449o2 (i+1)) + stT449o2 205 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 204
    simpa using h
  have hprev := st449o2_p204
  have hstep := st449o2_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p206 : ((7228140503537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 205, stT449o2 (i+1)) + stT449o2 206 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 205
    simpa using h
  have hprev := st449o2_p205
  have hstep := st449o2_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p207 : ((132354093673/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 206, stT449o2 (i+1)) + stT449o2 207 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 206
    simpa using h
  have hprev := st449o2_p206
  have hstep := st449o2_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p208 : ((264979186031/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 207, stT449o2 (i+1)) + stT449o2 208 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 207
    simpa using h
  have hprev := st449o2_p207
  have hstep := st449o2_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p209 : ((7236635473351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 208, stT449o2 (i+1)) + stT449o2 209 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 208
    simpa using h
  have hprev := st449o2_p208
  have hstep := st449o2_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p210 : ((3905504502953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 209, stT449o2 (i+1)) + stT449o2 210 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 209
    simpa using h
  have hprev := st449o2_p209
  have hstep := st449o2_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p211 : ((7753838419601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 210, stT449o2 (i+1)) + stT449o2 211 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 210
    simpa using h
  have hprev := st449o2_p210
  have hstep := st449o2_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p212 : ((7128453464679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 211, stT449o2 (i+1)) + stT449o2 212 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 211
    simpa using h
  have hprev := st449o2_p211
  have hstep := st449o2_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p213 : ((1643714952113/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 212, stT449o2 (i+1)) + stT449o2 213 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 212
    simpa using h
  have hprev := st449o2_p212
  have hstep := st449o2_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p214 : ((6650525148517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 213, stT449o2 (i+1)) + stT449o2 214 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 213
    simpa using h
  have hprev := st449o2_p213
  have hstep := st449o2_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p215 : ((7275085705801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 214, stT449o2 (i+1)) + stT449o2 215 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 214
    simpa using h
  have hprev := st449o2_p214
  have hstep := st449o2_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p216 : ((7825421430939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 215, stT449o2 (i+1)) + stT449o2 216 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 215
    simpa using h
  have hprev := st449o2_p215
  have hstep := st449o2_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p217 : ((7761193190109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 216, stT449o2 (i+1)) + stT449o2 217 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 216
    simpa using h
  have hprev := st449o2_p216
  have hstep := st449o2_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p218 : ((7149515207643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 217, stT449o2 (i+1)) + stT449o2 218 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 217
    simpa using h
  have hprev := st449o2_p217
  have hstep := st449o2_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p219 : ((6585574681053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 218, stT449o2 (i+1)) + stT449o2 219 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 218
    simpa using h
  have hprev := st449o2_p218
  have hstep := st449o2_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p220 : ((6609499306767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 219, stT449o2 (i+1)) + stT449o2 220 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 219
    simpa using h
  have hprev := st449o2_p219
  have hstep := st449o2_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p221 : ((7194189845199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 220, stT449o2 (i+1)) + stT449o2 221 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 220
    simpa using h
  have hprev := st449o2_p220
  have hstep := st449o2_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p222 : ((7784297046639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 221, stT449o2 (i+1)) + stT449o2 222 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 221
    simpa using h
  have hprev := st449o2_p221
  have hstep := st449o2_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p223 : ((7828011733359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 222, stT449o2 (i+1)) + stT449o2 223 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 222
    simpa using h
  have hprev := st449o2_p222
  have hstep := st449o2_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p224 : ((7288758671193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 223, stT449o2 (i+1)) + stT449o2 224 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 223
    simpa using h
  have hprev := st449o2_p223
  have hstep := st449o2_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p225 : ((1666692423383/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 224, stT449o2 (i+1)) + stT449o2 225 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 224
    simpa using h
  have hprev := st449o2_p224
  have hstep := st449o2_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p226 : ((1632518900949/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 225, stT449o2 (i+1)) + stT449o2 226 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 225
    simpa using h
  have hprev := st449o2_p225
  have hstep := st449o2_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p227 : ((6998830636269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 226, stT449o2 (i+1)) + stT449o2 227 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 226
    simpa using h
  have hprev := st449o2_p226
  have hstep := st449o2_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p228 : ((7647826150161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 227, stT449o2 (i+1)) + stT449o2 228 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 227
    simpa using h
  have hprev := st449o2_p227
  have hstep := st449o2_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p229 : ((7897817564469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 228, stT449o2 (i+1)) + stT449o2 229 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 228
    simpa using h
  have hprev := st449o2_p228
  have hstep := st449o2_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p230 : ((7530824562537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 229, stT449o2 (i+1)) + stT449o2 230 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 229
    simpa using h
  have hprev := st449o2_p229
  have hstep := st449o2_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p231 : ((6872854139881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 230, stT449o2 (i+1)) + stT449o2 231 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 230
    simpa using h
  have hprev := st449o2_p230
  have hstep := st449o2_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p232 : ((1299593183697/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 231, stT449o2 (i+1)) + stT449o2 232 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 231
    simpa using h
  have hprev := st449o2_p231
  have hstep := st449o2_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p233 : ((6727439081881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 232, stT449o2 (i+1)) + stT449o2 233 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 232
    simpa using h
  have hprev := st449o2_p232
  have hstep := st449o2_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p234 : ((7360574746521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 233, stT449o2 (i+1)) + stT449o2 234 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 233
    simpa using h
  have hprev := st449o2_p233
  have hstep := st449o2_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p235 : ((7856961781137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 234, stT449o2 (i+1)) + stT449o2 235 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 234
    simpa using h
  have hprev := st449o2_p234
  have hstep := st449o2_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p236 : ((7799431262037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 235, stT449o2 (i+1)) + stT449o2 236 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 235
    simpa using h
  have hprev := st449o2_p235
  have hstep := st449o2_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p237 : ((7239965065447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 236, stT449o2 (i+1)) + stT449o2 237 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 236
    simpa using h
  have hprev := st449o2_p236
  have hstep := st449o2_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p238 : ((1329202110923/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 237, stT449o2 (i+1)) + stT449o2 238 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 237
    simpa using h
  have hprev := st449o2_p237
  have hstep := st449o2_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p239 : ((6506502474737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 238, stT449o2 (i+1)) + stT449o2 239 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 238
    simpa using h
  have hprev := st449o2_p238
  have hstep := st449o2_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p240 : ((6932123831627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 239, stT449o2 (i+1)) + stT449o2 240 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 239
    simpa using h
  have hprev := st449o2_p239
  have hstep := st449o2_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p241 : ((7574045254463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 240, stT449o2 (i+1)) + stT449o2 241 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 240
    simpa using h
  have hprev := st449o2_p240
  have hstep := st449o2_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p242 : ((7914635908503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 241, stT449o2 (i+1)) + stT449o2 242 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 241
    simpa using h
  have hprev := st449o2_p241
  have hstep := st449o2_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p243 : ((1921060045713/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 242, stT449o2 (i+1)) + stT449o2 243 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 242
    simpa using h
  have hprev := st449o2_p242
  have hstep := st449o2_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p244 : ((3534611707971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 243, stT449o2 (i+1)) + stT449o2 244 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 243
    simpa using h
  have hprev := st449o2_p243
  have hstep := st449o2_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p245 : ((6555486448317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 244, stT449o2 (i+1)) + stT449o2 245 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 244
    simpa using h
  have hprev := st449o2_p244
  have hstep := st449o2_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p246 : ((3271463409497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 245, stT449o2 (i+1)) + stT449o2 246 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 245
    simpa using h
  have hprev := st449o2_p245
  have hstep := st449o2_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p247 : ((3518887215027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 246, stT449o2 (i+1)) + stT449o2 247 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 246
    simpa using h
  have hprev := st449o2_p246
  have hstep := st449o2_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p248 : ((3828199525027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 247, stT449o2 (i+1)) + stT449o2 248 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 247
    simpa using h
  have hprev := st449o2_p247
  have hstep := st449o2_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p249 : ((3963151050827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 248, stT449o2 (i+1)) + stT449o2 249 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 248
    simpa using h
  have hprev := st449o2_p248
  have hstep := st449o2_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p250 : ((3822801158727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 249, stT449o2 (i+1)) + stT449o2 250 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 249
    simpa using h
  have hprev := st449o2_p249
  have hstep := st449o2_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p251 : ((3514439678207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 250, stT449o2 (i+1)) + stT449o2 251 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 250
    simpa using h
  have hprev := st449o2_p250
  have hstep := st449o2_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p252 : ((6538172325821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 251, stT449o2 (i+1)) + stT449o2 252 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 251
    simpa using h
  have hprev := st449o2_p251
  have hstep := st449o2_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p253 : ((1633932147089/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 252, stT449o2 (i+1)) + stT449o2 253 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 252
    simpa using h
  have hprev := st449o2_p252
  have hstep := st449o2_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p254 : ((1755002099159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 253, stT449o2 (i+1)) + stT449o2 254 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 253
    simpa using h
  have hprev := st449o2_p253
  have hstep := st449o2_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p255 : ((1908640521543/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 254, stT449o2 (i+1)) + stT449o2 255 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 254
    simpa using h
  have hprev := st449o2_p254
  have hstep := st449o2_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p256 : ((1983408959043/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 255, stT449o2 (i+1)) + stT449o2 256 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 255
    simpa using h
  have hprev := st449o2_p255
  have hstep := st449o2_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p257 : ((3852213386411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 256, stT449o2 (i+1)) + stT449o2 257 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 256
    simpa using h
  have hprev := st449o2_p256
  have hstep := st449o2_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p258 : ((3556983044081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 257, stT449o2 (i+1)) + stT449o2 258 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 257
    simpa using h
  have hprev := st449o2_p257
  have hstep := st449o2_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p259 : ((3291411370191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 258, stT449o2 (i+1)) + stT449o2 259 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 258
    simpa using h
  have hprev := st449o2_p258
  have hstep := st449o2_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p260 : ((3242016991787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 259, stT449o2 (i+1)) + stT449o2 260 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 259
    simpa using h
  have hprev := st449o2_p259
  have hstep := st449o2_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p261 : ((3441828121907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 260, stT449o2 (i+1)) + stT449o2 261 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 260
    simpa using h
  have hprev := st449o2_p260
  have hstep := st449o2_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p262 : ((3750696996203/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 261, stT449o2 (i+1)) + stT449o2 262 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 261
    simpa using h
  have hprev := st449o2_p261
  have hstep := st449o2_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p263 : ((123604897099/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 262, stT449o2 (i+1)) + stT449o2 263 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 262
    simpa using h
  have hprev := st449o2_p262
  have hstep := st449o2_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p264 : ((1958329277251/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 263, stT449o2 (i+1)) + stT449o2 264 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 263
    simpa using h
  have hprev := st449o2_p263
  have hstep := st449o2_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p265 : ((1831224984743/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 264, stT449o2 (i+1)) + stT449o2 265 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 264
    simpa using h
  have hprev := st449o2_p264
  have hstep := st449o2_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p266 : ((1682682009503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 265, stT449o2 (i+1)) + stT449o2 266 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 265
    simpa using h
  have hprev := st449o2_p265
  have hstep := st449o2_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p267 : ((806091853129/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 266, stT449o2 (i+1)) + stT449o2 267 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 266
    simpa using h
  have hprev := st449o2_p266
  have hstep := st449o2_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p268 : ((1666034145237/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 267, stT449o2 (i+1)) + stT449o2 268 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 267
    simpa using h
  have hprev := st449o2_p267
  have hstep := st449o2_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p269 : ((3615808118609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 268, stT449o2 (i+1)) + stT449o2 269 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 268
    simpa using h
  have hprev := st449o2_p268
  have hstep := st449o2_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p270 : ((3888615666629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 269, stT449o2 (i+1)) + stT449o2 270 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 269
    simpa using h
  have hprev := st449o2_p269
  have hstep := st449o2_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p271 : ((3973135575829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 270, stT449o2 (i+1)) + stT449o2 271 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 270
    simpa using h
  have hprev := st449o2_p270
  have hstep := st449o2_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p272 : ((3815996198259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 271, stT449o2 (i+1)) + stT449o2 272 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 271
    simpa using h
  have hprev := st449o2_p271
  have hstep := st449o2_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p273 : ((3519527380757/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 272, stT449o2 (i+1)) + stT449o2 273 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 272
    simpa using h
  have hprev := st449o2_p272
  have hstep := st449o2_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p274 : ((6546900522457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 273, stT449o2 (i+1)) + stT449o2 274 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 273
    simpa using h
  have hprev := st449o2_p273
  have hstep := st449o2_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p275 : ((808271653803/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 274, stT449o2 (i+1)) + stT449o2 275 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 274
    simpa using h
  have hprev := st449o2_p274
  have hstep := st449o2_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p276 : ((6844943674893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 275, stT449o2 (i+1)) + stT449o2 276 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 275
    simpa using h
  have hprev := st449o2_p275
  have hstep := st449o2_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p277 : ((1860979765897/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 276, stT449o2 (i+1)) + stT449o2 277 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 276
    simpa using h
  have hprev := st449o2_p276
  have hstep := st449o2_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p278 : ((1972620891577/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 277, stT449o2 (i+1)) + stT449o2 278 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 277
    simpa using h
  have hprev := st449o2_p277
  have hstep := st449o2_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p279 : ((197768321381/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 278, stT449o2 (i+1)) + stT449o2 279 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 278
    simpa using h
  have hprev := st449o2_p278
  have hstep := st449o2_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p280 : ((1498991431873/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 279, stT449o2 (i+1)) + stT449o2 280 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 279
    simpa using h
  have hprev := st449o2_p279
  have hstep := st449o2_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p281 : ((1379675585683/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 280, stT449o2 (i+1)) + stT449o2 281 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 280
    simpa using h
  have hprev := st449o2_p280
  have hstep := st449o2_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p282 : ((6481937867483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 281, stT449o2 (i+1)) + stT449o2 282 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 281
    simpa using h
  have hprev := st449o2_p281
  have hstep := st449o2_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p283 : ((6493979398049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 282, stT449o2 (i+1)) + stT449o2 283 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 282
    simpa using h
  have hprev := st449o2_p282
  have hstep := st449o2_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p284 : ((6924637531059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 283, stT449o2 (i+1)) + stT449o2 284 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 283
    simpa using h
  have hprev := st449o2_p283
  have hstep := st449o2_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p285 : ((7516680471839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 284, stT449o2 (i+1)) + stT449o2 285 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 284
    simpa using h
  have hprev := st449o2_p284
  have hstep := st449o2_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p286 : ((7921409883359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 285, stT449o2 (i+1)) + stT449o2 286 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 285
    simpa using h
  have hprev := st449o2_p285
  have hstep := st449o2_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p287 : ((7903873195421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 286, stT449o2 (i+1)) + stT449o2 287 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 286
    simpa using h
  have hprev := st449o2_p286
  have hstep := st449o2_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p288 : ((7476842318501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 287, stT449o2 (i+1)) + stT449o2 288 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 287
    simpa using h
  have hprev := st449o2_p287
  have hstep := st449o2_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p289 : ((6888671024461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 288, stT449o2 (i+1)) + stT449o2 289 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 288
    simpa using h
  have hprev := st449o2_p288
  have hstep := st449o2_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p290 : ((6476739016287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 289, stT449o2 (i+1)) + stT449o2 290 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 289
    simpa using h
  have hprev := st449o2_p289
  have hstep := st449o2_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p291 : ((3236999239931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 290, stT449o2 (i+1)) + stT449o2 291 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 290
    simpa using h
  have hprev := st449o2_p290
  have hstep := st449o2_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p292 : ((3439737660131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 291, stT449o2 (i+1)) + stT449o2 292 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 291
    simpa using h
  have hprev := st449o2_p291
  have hstep := st449o2_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p293 : ((746323615529/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 292, stT449o2 (i+1)) + stT449o2 293 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 292
    simpa using h
  have hprev := st449o2_p292
  have hstep := st449o2_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p294 : ((1974725734311/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 293, stT449o2 (i+1)) + stT449o2 294 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 293
    simpa using h
  have hprev := st449o2_p293
  have hstep := st449o2_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p295 : ((124158888807/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 294, stT449o2 (i+1)) + stT449o2 295 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 294
    simpa using h
  have hprev := st449o2_p294
  have hstep := st449o2_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p296 : ((7581380381053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 295, stT449o2 (i+1)) + stT449o2 296 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 295
    simpa using h
  have hprev := st449o2_p295
  have hstep := st449o2_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p297 : ((1401277794451/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 296, stT449o2 (i+1)) + stT449o2 297 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 296
    simpa using h
  have hprev := st449o2_p296
  have hstep := st449o2_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p298 : ((1306937756491/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 297, stT449o2 (i+1)) + stT449o2 298 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 297
    simpa using h
  have hprev := st449o2_p297
  have hstep := st449o2_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p299 : ((1284032318623/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 298, stT449o2 (i+1)) + stT449o2 299 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 298
    simpa using h
  have hprev := st449o2_p298
  have hstep := st449o2_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p300 : ((1344408810343/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 299, stT449o2 (i+1)) + stT449o2 300 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 299
    simpa using h
  have hprev := st449o2_p299
  have hstep := st449o2_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p301 : ((1455398699299/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 300, stT449o2 (i+1)) + stT449o2 301 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 300
    simpa using h
  have hprev := st449o2_p300
  have hstep := st449o2_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p302 : ((1557938454211/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 301, stT449o2 (i+1)) + stT449o2 302 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 301
    simpa using h
  have hprev := st449o2_p301
  have hstep := st449o2_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p303 : ((1598133376239/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 302, stT449o2 (i+1)) + stT449o2 303 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 302
    simpa using h
  have hprev := st449o2_p302
  have hstep := st449o2_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p304 : ((1555339836219/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 303, stT449o2 (i+1)) + stT449o2 304 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 303
    simpa using h
  have hprev := st449o2_p303
  have hstep := st449o2_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p305 : ((3630697504817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 304, stT449o2 (i+1)) + stT449o2 305 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 304
    simpa using h
  have hprev := st449o2_p304
  have hstep := st449o2_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p306 : ((1678134866281/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 305, stT449o2 (i+1)) + stT449o2 306 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 305
    simpa using h
  have hprev := st449o2_p305
  have hstep := st449o2_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p307 : ((6411891501137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 306, stT449o2 (i+1)) + stT449o2 307 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 306
    simpa using h
  have hprev := st449o2_p306
  have hstep := st449o2_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p308 : ((6511254143699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 307, stT449o2 (i+1)) + stT449o2 308 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 307
    simpa using h
  have hprev := st449o2_p307
  have hstep := st449o2_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p309 : ((6957919377779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 308, stT449o2 (i+1)) + stT449o2 309 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 308
    simpa using h
  have hprev := st449o2_p308
  have hstep := st449o2_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p310 : ((752490973243/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 309, stT449o2 (i+1)) + stT449o2 310 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 309
    simpa using h
  have hprev := st449o2_p309
  have hstep := st449o2_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p311 : ((7927741622371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 310, stT449o2 (i+1)) + stT449o2 311 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 310
    simpa using h
  have hprev := st449o2_p310
  have hstep := st449o2_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p312 : ((7967000461981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 311, stT449o2 (i+1)) + stT449o2 312 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 311
    simpa using h
  have hprev := st449o2_p311
  have hstep := st449o2_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p313 : ((1525074719523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 312, stT449o2 (i+1)) + stT449o2 313 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 312
    simpa using h
  have hprev := st449o2_p312
  have hstep := st449o2_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p314 : ((3536456799801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 313, stT449o2 (i+1)) + stT449o2 314 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 313
    simpa using h
  have hprev := st449o2_p313
  have hstep := st449o2_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p315 : ((1645157137709/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 314, stT449o2 (i+1)) + stT449o2 315 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 314
    simpa using h
  have hprev := st449o2_p314
  have hstep := st449o2_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p316 : ((1596778916253/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 315, stT449o2 (i+1)) + stT449o2 316 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 315
    simpa using h
  have hprev := st449o2_p315
  have hstep := st449o2_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p317 : ((6583993153817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 316, stT449o2 (i+1)) + stT449o2 317 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 316
    simpa using h
  have hprev := st449o2_p316
  have hstep := st449o2_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p318 : ((7074597435773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 317, stT449o2 (i+1)) + stT449o2 318 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 317
    simpa using h
  have hprev := st449o2_p317
  have hstep := st449o2_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p319 : ((7623371100437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 318, stT449o2 (i+1)) + stT449o2 319 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 318
    simpa using h
  have hprev := st449o2_p318
  have hstep := st449o2_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p320 : ((7969953753229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 319, stT449o2 (i+1)) + stT449o2 320 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 319
    simpa using h
  have hprev := st449o2_p319
  have hstep := st449o2_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p321 : ((1590447751467/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 320, stT449o2 (i+1)) + stT449o2 321 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 320
    simpa using h
  have hprev := st449o2_p320
  have hstep := st449o2_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p322 : ((7580587163119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 321, stT449o2 (i+1)) + stT449o2 322 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 321
    simpa using h
  have hprev := st449o2_p321
  have hstep := st449o2_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p323 : ((439372395169/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 322, stT449o2 (i+1)) + stT449o2 323 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 322
    simpa using h
  have hprev := st449o2_p322
  have hstep := st449o2_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p324 : ((1639024624793/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 323, stT449o2 (i+1)) + stT449o2 324 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 323
    simpa using h
  have hprev := st449o2_p323
  have hstep := st449o2_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p325 : ((1594121578843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 324, stT449o2 (i+1)) + stT449o2 325 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 324
    simpa using h
  have hprev := st449o2_p324
  have hstep := st449o2_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p326 : ((1642893710647/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 325, stT449o2 (i+1)) + stT449o2 326 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 325
    simpa using h
  have hprev := st449o2_p325
  have hstep := st449o2_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p327 : ((7050576013773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 326, stT449o2 (i+1)) + stT449o2 327 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 326
    simpa using h
  have hprev := st449o2_p326
  have hstep := st449o2_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p328 : ((1898861549461/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 327, stT449o2 (i+1)) + stT449o2 328 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 327
    simpa using h
  have hprev := st449o2_p327
  have hstep := st449o2_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p329 : ((1592208538801/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 328, stT449o2 (i+1)) + stT449o2 329 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 328
    simpa using h
  have hprev := st449o2_p328
  have hstep := st449o2_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p330 : ((798507944687/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 329, stT449o2 (i+1)) + stT449o2 330 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 329
    simpa using h
  have hprev := st449o2_p329
  have hstep := st449o2_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p331 : ((191469314473/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 330, stT449o2 (i+1)) + stT449o2 331 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 330
    simpa using h
  have hprev := st449o2_p330
  have hstep := st449o2_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p332 : ((712809189013/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 331, stT449o2 (i+1)) + stT449o2 332 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 331
    simpa using h
  have hprev := st449o2_p331
  have hstep := st449o2_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p333 : ((1325412194603/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 332, stT449o2 (i+1)) + stT449o2 333 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 332
    simpa using h
  have hprev := st449o2_p332
  have hstep := st449o2_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p334 : ((6374126678311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 333, stT449o2 (i+1)) + stT449o2 334 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 333
    simpa using h
  have hprev := st449o2_p333
  have hstep := st449o2_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p335 : ((259106089249/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 334, stT449o2 (i+1)) + stT449o2 335 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 334
    simpa using h
  have hprev := st449o2_p334
  have hstep := st449o2_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p336 : ((6891001645777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 335, stT449o2 (i+1)) + stT449o2 336 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 335
    simpa using h
  have hprev := st449o2_p335
  have hstep := st449o2_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p337 : ((7435186009171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 336, stT449o2 (i+1)) + stT449o2 337 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 336
    simpa using h
  have hprev := st449o2_p336
  have hstep := st449o2_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p338 : ((1575482940631/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 337, stT449o2 (i+1)) + stT449o2 338 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 337
    simpa using h
  have hprev := st449o2_p337
  have hstep := st449o2_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p339 : ((1606141260631/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 338, stT449o2 (i+1)) + stT449o2 339 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 338
    simpa using h
  have hprev := st449o2_p338
  have hstep := st449o2_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p340 : ((1957999287007/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 339, stT449o2 (i+1)) + stT449o2 340 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 339
    simpa using h
  have hprev := st449o2_p339
  have hstep := st449o2_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p341 : ((230202966697/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 340, stT449o2 (i+1)) + stT449o2 341 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 340
    simpa using h
  have hprev := st449o2_p340
  have hstep := st449o2_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p342 : ((3414841390461/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 341, stT449o2 (i+1)) + stT449o2 342 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 341
    simpa using h
  have hprev := st449o2_p341
  have hstep := st449o2_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p343 : ((3222230966411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 342, stT449o2 (i+1)) + stT449o2 343 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 342
    simpa using h
  have hprev := st449o2_p342
  have hstep := st449o2_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p344 : ((3184397289367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 343, stT449o2 (i+1)) + stT449o2 344 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 343
    simpa using h
  have hprev := st449o2_p343
  have hstep := st449o2_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p345 : ((3316013138913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 344, stT449o2 (i+1)) + stT449o2 345 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 344
    simpa using h
  have hprev := st449o2_p344
  have hstep := st449o2_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p346 : ((7125023819313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 345, stT449o2 (i+1)) + stT449o2 346 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 345
    simpa using h
  have hprev := st449o2_p345
  have hstep := st449o2_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p347 : ((7646717564337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 346, stT449o2 (i+1)) + stT449o2 347 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 346
    simpa using h
  have hprev := st449o2_p346
  have hstep := st449o2_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p348 : ((7986647827729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 347, stT449o2 (i+1)) + stT449o2 348 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 347
    simpa using h
  have hprev := st449o2_p347
  have hstep := st449o2_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p349 : ((8009496018037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 348, stT449o2 (i+1)) + stT449o2 349 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 348
    simpa using h
  have hprev := st449o2_p348
  have hstep := st449o2_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p350 : ((7707834755849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 349, stT449o2 (i+1)) + stT449o2 350 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 349
    simpa using h
  have hprev := st449o2_p349
  have hstep := st449o2_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p351 : ((3601482852509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 350, stT449o2 (i+1)) + stT449o2 351 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 350
    simpa using h
  have hprev := st449o2_p350
  have hstep := st449o2_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p352 : ((418438658127/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 351, stT449o2 (i+1)) + stT449o2 352 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 351
    simpa using h
  have hprev := st449o2_p351
  have hstep := st449o2_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p353 : ((6383180867449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 352, stT449o2 (i+1)) + stT449o2 353 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 352
    simpa using h
  have hprev := st449o2_p352
  have hstep := st449o2_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p354 : ((6388029687211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 353, stT449o2 (i+1)) + stT449o2 354 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 353
    simpa using h
  have hprev := st449o2_p353
  have hstep := st449o2_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p355 : ((6706000009843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 354, stT449o2 (i+1)) + stT449o2 355 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 354
    simpa using h
  have hprev := st449o2_p354
  have hstep := st449o2_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p356 : ((7212793107409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 355, stT449o2 (i+1)) + stT449o2 356 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 355
    simpa using h
  have hprev := st449o2_p355
  have hstep := st449o2_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p357 : ((7712968077977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 356, stT449o2 (i+1)) + stT449o2 357 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 356
    simpa using h
  have hprev := st449o2_p356
  have hstep := st449o2_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p358 : ((8015684073233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 357, stT449o2 (i+1)) + stT449o2 358 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 357
    simpa using h
  have hprev := st449o2_p357
  have hstep := st449o2_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p359 : ((8007064370273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 358, stT449o2 (i+1)) + stT449o2 359 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 358
    simpa using h
  have hprev := st449o2_p358
  have hstep := st449o2_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p360 : ((7691960888571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 359, stT449o2 (i+1)) + stT449o2 360 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 359
    simpa using h
  have hprev := st449o2_p359
  have hstep := st449o2_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p361 : ((7190271740527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 360, stT449o2 (i+1)) + stT449o2 361 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 360
    simpa using h
  have hprev := st449o2_p360
  have hstep := st449o2_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p362 : ((6690314664879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 361, stT449o2 (i+1)) + stT449o2 362 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 361
    simpa using h
  have hprev := st449o2_p361
  have hstep := st449o2_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p363 : ((6377795418223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 362, stT449o2 (i+1)) + stT449o2 363 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 362
    simpa using h
  have hprev := st449o2_p362
  have hstep := st449o2_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p364 : ((3183607271741/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 363, stT449o2 (i+1)) + stT449o2 364 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 363
    simpa using h
  have hprev := st449o2_p363
  have hstep := st449o2_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p365 : ((1665227058907/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 364, stT449o2 (i+1)) + stT449o2 365 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 364
    simpa using h
  have hprev := st449o2_p364
  have hstep := st449o2_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p366 : ((11171777557/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 365, stT449o2 (i+1)) + stT449o2 366 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 365
    simpa using h
  have hprev := st449o2_p365
  have hstep := st449o2_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p367 : ((1531090128871/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 366, stT449o2 (i+1)) + stT449o2 367 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 366
    simpa using h
  have hprev := st449o2_p366
  have hstep := st449o2_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p368 : ((7994483590463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 367, stT449o2 (i+1)) + stT449o2 368 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 367
    simpa using h
  have hprev := st449o2_p367
  have hstep := st449o2_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p369 : ((2011467616033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 368, stT449o2 (i+1)) + stT449o2 369 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 368
    simpa using h
  have hprev := st449o2_p368
  have hstep := st449o2_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p370 : ((487041196231/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 369, stT449o2 (i+1)) + stT449o2 370 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 369
    simpa using h
  have hprev := st449o2_p369
  have hstep := st449o2_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p371 : ((1831638552049/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 370, stT449o2 (i+1)) + stT449o2 371 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 370
    simpa using h
  have hprev := st449o2_p370
  have hstep := st449o2_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p372 : ((425858002573/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 371, stT449o2 (i+1)) + stT449o2 372 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 371
    simpa using h
  have hprev := st449o2_p371
  have hstep := st449o2_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p373 : ((1608782161273/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 372, stT449o2 (i+1)) + stT449o2 373 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 372
    simpa using h
  have hprev := st449o2_p372
  have hstep := st449o2_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p374 : ((1580697560729/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 373, stT449o2 (i+1)) + stT449o2 374 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 373
    simpa using h
  have hprev := st449o2_p373
  have hstep := st449o2_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p375 : ((1628640891003/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 374, stT449o2 (i+1)) + stT449o2 375 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 374
    simpa using h
  have hprev := st449o2_p374
  have hstep := st449o2_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p376 : ((1735593472193/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 375, stT449o2 (i+1)) + stT449o2 376 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 375
    simpa using h
  have hprev := st449o2_p375
  have hstep := st449o2_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p377 : ((466085626079/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 376, stT449o2 (i+1)) + stT449o2 377 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 376
    simpa using h
  have hprev := st449o2_p376
  have hstep := st449o2_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p378 : ((492641463971/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 377, stT449o2 (i+1)) + stT449o2 378 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 377
    simpa using h
  have hprev := st449o2_p377
  have hstep := st449o2_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p379 : ((2018080382049/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 378, stT449o2 (i+1)) + stT449o2 379 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 378
    simpa using h
  have hprev := st449o2_p378
  have hstep := st449o2_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p380 : ((3982054426323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 379, stT449o2 (i+1)) + stT449o2 380 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 379
    simpa using h
  have hprev := st449o2_p379
  have hstep := st449o2_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p381 : ((3797839681413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 380, stT449o2 (i+1)) + stT449o2 381 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 380
    simpa using h
  have hprev := st449o2_p380
  have hstep := st449o2_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p382 : ((7092258032911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 381, stT449o2 (i+1)) + stT449o2 382 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 381
    simpa using h
  have hprev := st449o2_p381
  have hstep := st449o2_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p383 : ((3311507539693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 382, stT449o2 (i+1)) + stT449o2 383 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 382
    simpa using h
  have hprev := st449o2_p382
  have hstep := st449o2_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p384 : ((3172027295929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 383, stT449o2 (i+1)) + stT449o2 384 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 383
    simpa using h
  have hprev := st449o2_p383
  have hstep := st449o2_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p385 : ((1586718744589/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 384, stT449o2 (i+1)) + stT449o2 385 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 384
    simpa using h
  have hprev := st449o2_p384
  have hstep := st449o2_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p386 : ((1657289144503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 385, stT449o2 (i+1)) + stT449o2 386 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 385
    simpa using h
  have hprev := st449o2_p385
  have hstep := st449o2_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p387 : ((354846661007/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 386, stT449o2 (i+1)) + stT449o2 387 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 386
    simpa using h
  have hprev := st449o2_p386
  have hstep := st449o2_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p388 : ((7596616970139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 387, stT449o2 (i+1)) + stT449o2 388 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 387
    simpa using h
  have hprev := st449o2_p387
  have hstep := st449o2_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p389 : ((7965763528559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 388, stT449o2 (i+1)) + stT449o2 389 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 388
    simpa using h
  have hprev := st449o2_p388
  have hstep := st449o2_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p390 : ((4042853829979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 389, stT449o2 (i+1)) + stT449o2 390 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 389
    simpa using h
  have hprev := st449o2_p389
  have hstep := st449o2_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p391 : ((791908035251/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 390, stT449o2 (i+1)) + stT449o2 391 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 390
    simpa using h
  have hprev := st449o2_p390
  have hstep := st449o2_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p392 : ((3760280228677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 391, stT449o2 (i+1)) + stT449o2 392 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 391
    simpa using h
  have hprev := st449o2_p391
  have hstep := st449o2_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p393 : ((3509064025733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 392, stT449o2 (i+1)) + stT449o2 393 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 392
    simpa using h
  have hprev := st449o2_p392
  have hstep := st449o2_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p394 : ((657143898043/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 393, stT449o2 (i+1)) + stT449o2 394 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 393
    simpa using h
  have hprev := st449o2_p393
  have hstep := st449o2_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p395 : ((126420414991/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 394, stT449o2 (i+1)) + stT449o2 395 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 394
    simpa using h
  have hprev := st449o2_p394
  have hstep := st449o2_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p396 : ((3172243667557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 395, stT449o2 (i+1)) + stT449o2 396 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 395
    simpa using h
  have hprev := st449o2_p395
  have hstep := st449o2_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p397 : ((6633190156859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 396, stT449o2 (i+1)) + stT449o2 397 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 396
    simpa using h
  have hprev := st449o2_p396
  have hstep := st449o2_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p398 : ((7096196972897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 397, stT449o2 (i+1)) + stT449o2 398 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 397
    simpa using h
  have hprev := st449o2_p397
  have hstep := st449o2_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p399 : ((7589554384003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 398, stT449o2 (i+1)) + stT449o2 399 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 398
    simpa using h
  have hprev := st449o2_p398
  have hstep := st449o2_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p400 : ((7961361384003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 399, stT449o2 (i+1)) + stT449o2 400 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 399
    simpa using h
  have hprev := st449o2_p399
  have hstep := st449o2_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p401 : ((8098372180867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 400, stT449o2 (i+1)) + stT449o2 401 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 400
    simpa using h
  have hprev := st449o2_p400
  have hstep := st449o2_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p402 : ((7959957693267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 401, stT449o2 (i+1)) + stT449o2 402 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 401
    simpa using h
  have hprev := st449o2_p401
  have hstep := st449o2_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p403 : ((7589355468259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 402, stT449o2 (i+1)) + stT449o2 403 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 402
    simpa using h
  have hprev := st449o2_p402
  have hstep := st449o2_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p404 : ((709945298663/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 403, stT449o2 (i+1)) + stT449o2 404 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 403
    simpa using h
  have hprev := st449o2_p403
  have hstep := st449o2_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p405 : ((3318941418131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 404, stT449o2 (i+1)) + stT449o2 405 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 404
    simpa using h
  have hprev := st449o2_p404
  have hstep := st449o2_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p406 : ((3171208193323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 405, stT449o2 (i+1)) + stT449o2 406 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 405
    simpa using h
  have hprev := st449o2_p405
  have hstep := st449o2_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p407 : ((315006413409/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 406, stT449o2 (i+1)) + stT449o2 407 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 406
    simpa using h
  have hprev := st449o2_p406
  have hstep := st449o2_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p408 : ((652235168569/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 407, stT449o2 (i+1)) + stT449o2 408 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 407
    simpa using h
  have hprev := st449o2_p407
  have hstep := st449o2_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p409 : ((694240225169/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 408, stT449o2 (i+1)) + stT449o2 409 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 408
    simpa using h
  have hprev := st449o2_p408
  have hstep := st449o2_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p410 : ((3718113865149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 409, stT449o2 (i+1)) + stT449o2 410 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 409
    simpa using h
  have hprev := st449o2_p409
  have hstep := st449o2_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p411 : ((7859413349151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 410, stT449o2 (i+1)) + stT449o2 411 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 410
    simpa using h
  have hprev := st449o2_p410
  have hstep := st449o2_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p412 : ((8089408118247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 411, stT449o2 (i+1)) + stT449o2 412 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 411
    simpa using h
  have hprev := st449o2_p411
  have hstep := st449o2_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p413 : ((8060631981607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 412, stT449o2 (i+1)) + stT449o2 413 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 412
    simpa using h
  have hprev := st449o2_p412
  have hstep := st449o2_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p414 : ((311301394361/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 413, stT449o2 (i+1)) + stT449o2 414 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 413
    simpa using h
  have hprev := st449o2_p413
  have hstep := st449o2_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p415 : ((7335861620123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 414, stT449o2 (i+1)) + stT449o2 415 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 414
    simpa using h
  have hprev := st449o2_p414
  have hstep := st449o2_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p416 : ((1712161799037/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 415, stT449o2 (i+1)) + stT449o2 416 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 415
    simpa using h
  have hprev := st449o2_p415
  have hstep := st449o2_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p417 : ((51673918223/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 416, stT449o2 (i+1)) + stT449o2 417 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 416
    simpa using h
  have hprev := st449o2_p416
  have hstep := st449o2_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p418 : ((1255420552359/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 417, stT449o2 (i+1)) + stT449o2 418 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 417
    simpa using h
  have hprev := st449o2_p417
  have hstep := st449o2_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p419 : ((7940576389/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 418, stT449o2 (i+1)) + stT449o2 419 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 418
    simpa using h
  have hprev := st449o2_p418
  have hstep := st449o2_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p420 : ((133261362469/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 419, stT449o2 (i+1)) + stT449o2 420 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 419
    simpa using h
  have hprev := st449o2_p419
  have hstep := st449o2_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p421 : ((712139379567/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 420, stT449o2 (i+1)) + stT449o2 421 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 420
    simpa using h
  have hprev := st449o2_p420
  have hstep := st449o2_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p422 : ((3799891639479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 421, stT449o2 (i+1)) + stT449o2 422 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 421
    simpa using h
  have hprev := st449o2_p421
  have hstep := st449o2_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p423 : ((3983106093951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 422, stT449o2 (i+1)) + stT449o2 423 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 422
    simpa using h
  have hprev := st449o2_p422
  have hstep := st449o2_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p424 : ((4060292090863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 423, stT449o2 (i+1)) + stT449o2 424 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 423
    simpa using h
  have hprev := st449o2_p423
  have hstep := st449o2_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p425 : ((802166441891/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 424, stT449o2 (i+1)) + stT449o2 425 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 424
    simpa using h
  have hprev := st449o2_p424
  have hstep := st449o2_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p426 : ((3848740611849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 425, stT449o2 (i+1)) + stT449o2 426 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 425
    simpa using h
  have hprev := st449o2_p425
  have hstep := st449o2_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p427 : ((1809202119819/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 426, stT449o2 (i+1)) + stT449o2 427 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 426
    simpa using h
  have hprev := st449o2_p426
  have hstep := st449o2_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p428 : ((6764405671779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 427, stT449o2 (i+1)) + stT449o2 428 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 427
    simpa using h
  have hprev := st449o2_p427
  have hstep := st449o2_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p429 : ((6407062379079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 428, stT449o2 (i+1)) + stT449o2 429 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 428
    simpa using h
  have hprev := st449o2_p428
  have hstep := st449o2_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p430 : ((6259695669681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 429, stT449o2 (i+1)) + stT449o2 430 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 429
    simpa using h
  have hprev := st449o2_p429
  have hstep := st449o2_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p431 : ((6360538895829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 430, stT449o2 (i+1)) + stT449o2 431 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 430
    simpa using h
  have hprev := st449o2_p430
  have hstep := st449o2_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p432 : ((6681809152329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 431, stT449o2 (i+1)) + stT449o2 432 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 431
    simpa using h
  have hprev := st449o2_p431
  have hstep := st449o2_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p433 : ((7137888356089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 432, stT449o2 (i+1)) + stT449o2 433 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 432
    simpa using h
  have hprev := st449o2_p432
  have hstep := st449o2_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p434 : ((3804278011997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 433, stT449o2 (i+1)) + stT449o2 434 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 433
    simpa using h
  have hprev := st449o2_p433
  have hstep := st449o2_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p435 : ((7970853130147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 434, stT449o2 (i+1)) + stT449o2 435 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 434
    simpa using h
  have hprev := st449o2_p434
  have hstep := st449o2_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p436 : ((1016385082249/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 435, stT449o2 (i+1)) + stT449o2 436 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 435
    simpa using h
  have hprev := st449o2_p435
  have hstep := st449o2_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p437 : ((8048659803587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 436, stT449o2 (i+1)) + stT449o2 437 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 436
    simpa using h
  have hprev := st449o2_p436
  have hstep := st449o2_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p438 : ((1549172416147/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 437, stT449o2 (i+1)) + stT449o2 438 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 437
    simpa using h
  have hprev := st449o2_p437
  have hstep := st449o2_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p439 : ((7301304258887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 438, stT449o2 (i+1)) + stT449o2 439 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 438
    simpa using h
  have hprev := st449o2_p438
  have hstep := st449o2_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p440 : ((6829097399031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 439, stT449o2 (i+1)) + stT449o2 440 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 439
    simpa using h
  have hprev := st449o2_p439
  have hstep := st449o2_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p441 : ((806172301239/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 440, stT449o2 (i+1)) + stT449o2 441 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 440
    simpa using h
  have hprev := st449o2_p440
  have hstep := st449o2_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p442 : ((1564457980639/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 441, stT449o2 (i+1)) + stT449o2 442 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 441
    simpa using h
  have hprev := st449o2_p441
  have hstep := st449o2_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p443 : ((630189922117/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 442, stT449o2 (i+1)) + stT449o2 443 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 442
    simpa using h
  have hprev := st449o2_p442
  have hstep := st449o2_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p444 : ((656950426381/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 443, stT449o2 (i+1)) + stT449o2 444 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 443
    simpa using h
  have hprev := st449o2_p443
  have hstep := st449o2_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p445 : ((139857021983/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 444, stT449o2 (i+1)) + stT449o2 445 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 444
    simpa using h
  have hprev := st449o2_p444
  have hstep := st449o2_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p446 : ((7466010384939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 445, stT449o2 (i+1)) + stT449o2 446 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 445
    simpa using h
  have hprev := st449o2_p445
  have hstep := st449o2_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p447 : ((983954780103/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 446, stT449o2 (i+1)) + stT449o2 447 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 446
    simpa using h
  have hprev := st449o2_p446
  have hstep := st449o2_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p448 : ((8110041396099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 447, stT449o2 (i+1)) + stT449o2 448 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 447
    simpa using h
  have hprev := st449o2_p447
  have hstep := st449o2_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p449 : ((1624687325767/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 448, stT449o2 (i+1)) + stT449o2 449 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 448
    simpa using h
  have hprev := st449o2_p448
  have hstep := st449o2_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p450 : ((1581899402413/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 449, stT449o2 (i+1)) + stT449o2 450 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 449
    simpa using h
  have hprev := st449o2_p449
  have hstep := st449o2_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p451 : ((300848873653/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 450, stT449o2 (i+1)) + stT449o2 451 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 450
    simpa using h
  have hprev := st449o2_p450
  have hstep := st449o2_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p452 : ((7053389502061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 451, stT449o2 (i+1)) + stT449o2 452 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 451
    simpa using h
  have hprev := st449o2_p451
  have hstep := st449o2_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p453 : ((1323830046799/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 452, stT449o2 (i+1)) + stT449o2 453 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 452
    simpa using h
  have hprev := st449o2_p452
  have hstep := st449o2_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p454 : ((6322616312427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 453, stT449o2 (i+1)) + stT449o2 454 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 453
    simpa using h
  have hprev := st449o2_p453
  have hstep := st449o2_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p455 : ((6234108643683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 454, stT449o2 (i+1)) + stT449o2 455 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 454
    simpa using h
  have hprev := st449o2_p454
  have hstep := st449o2_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p456 : ((6373809513123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 455, stT449o2 (i+1)) + stT449o2 456 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 455
    simpa using h
  have hprev := st449o2_p455
  have hstep := st449o2_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p457 : ((6707636032323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 456, stT449o2 (i+1)) + stT449o2 457 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 456
    simpa using h
  have hprev := st449o2_p456
  have hstep := st449o2_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p458 : ((1431197809733/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 457, stT449o2 (i+1)) + stT449o2 458 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 457
    simpa using h
  have hprev := st449o2_p457
  have hstep := st449o2_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p459 : ((1522603233829/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 458, stT449o2 (i+1)) + stT449o2 459 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 458
    simpa using h
  have hprev := st449o2_p458
  have hstep := st449o2_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p460 : ((7971731341613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 459, stT449o2 (i+1)) + stT449o2 460 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 459
    simpa using h
  have hprev := st449o2_p459
  have hstep := st449o2_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p461 : ((8148947228867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 460, stT449o2 (i+1)) + stT449o2 461 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 460
    simpa using h
  have hprev := st449o2_p460
  have hstep := st449o2_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p462 : ((8104303441073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 461, stT449o2 (i+1)) + stT449o2 462 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 461
    simpa using h
  have hprev := st449o2_p461
  have hstep := st449o2_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p463 : ((7849020364853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 462, stT449o2 (i+1)) + stT449o2 463 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 462
    simpa using h
  have hprev := st449o2_p462
  have hstep := st449o2_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p464 : ((7442699822493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 463, stT449o2 (i+1)) + stT449o2 464 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 463
    simpa using h
  have hprev := st449o2_p463
  have hstep := st449o2_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p465 : ((6979046150469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 464, stT449o2 (i+1)) + stT449o2 465 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 464
    simpa using h
  have hprev := st449o2_p464
  have hstep := st449o2_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p466 : ((6564063312303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 465, stT449o2 (i+1)) + stT449o2 466 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 465
    simpa using h
  have hprev := st449o2_p465
  have hstep := st449o2_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p467 : ((3145908504599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 466, stT449o2 (i+1)) + stT449o2 467 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 466
    simpa using h
  have hprev := st449o2_p466
  have hstep := st449o2_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p468 : ((777912424059/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 467, stT449o2 (i+1)) + stT449o2 468 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 467
    simpa using h
  have hprev := st449o2_p467
  have hstep := st449o2_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p469 : ((1274622274359/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 468, stT449o2 (i+1)) + stT449o2 469 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 468
    simpa using h
  have hprev := st449o2_p468
  have hstep := st449o2_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p470 : ((670674203997/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 469, stT449o2 (i+1)) + stT449o2 470 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 469
    simpa using h
  have hprev := st449o2_p469
  have hstep := st449o2_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p471 : ((1429781175389/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 470, stT449o2 (i+1)) + stT449o2 471 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 470
    simpa using h
  have hprev := st449o2_p470
  have hstep := st449o2_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p472 : ((304031521453/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 471, stT449o2 (i+1)) + stT449o2 472 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 471
    simpa using h
  have hprev := st449o2_p471
  have hstep := st449o2_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p473 : ((63697843033/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 472, stT449o2 (i+1)) + stT449o2 473 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 472
    simpa using h
  have hprev := st449o2_p472
  have hstep := st449o2_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p474 : ((407692209781/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 473, stT449o2 (i+1)) + stT449o2 474 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 473
    simpa using h
  have hprev := st449o2_p473
  have hstep := st449o2_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p475 : ((2033553496541/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 474, stT449o2 (i+1)) + stT449o2 475 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 474
    simpa using h
  have hprev := st449o2_p474
  have hstep := st449o2_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p476 : ((3954244951657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 475, stT449o2 (i+1)) + stT449o2 476 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 475
    simpa using h
  have hprev := st449o2_p475
  have hstep := st449o2_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p477 : ((7526683475201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 476, stT449o2 (i+1)) + stT449o2 477 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 476
    simpa using h
  have hprev := st449o2_p476
  have hstep := st449o2_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p478 : ((7072271998881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 477, stT449o2 (i+1)) + stT449o2 478 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 477
    simpa using h
  have hprev := st449o2_p477
  have hstep := st449o2_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p479 : ((6643753881297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 478, stT449o2 (i+1)) + stT449o2 479 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 478
    simpa using h
  have hprev := st449o2_p478
  have hstep := st449o2_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p480 : ((6333261922989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 479, stT449o2 (i+1)) + stT449o2 480 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 479
    simpa using h
  have hprev := st449o2_p479
  have hstep := st449o2_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p481 : ((6206866798023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 480, stT449o2 (i+1)) + stT449o2 481 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 480
    simpa using h
  have hprev := st449o2_p480
  have hstep := st449o2_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p482 : ((6290822161863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 481, stT449o2 (i+1)) + stT449o2 482 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 481
    simpa using h
  have hprev := st449o2_p481
  have hstep := st449o2_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p483 : ((6566424747363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 482, stT449o2 (i+1)) + stT449o2 483 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 482
    simpa using h
  have hprev := st449o2_p482
  have hstep := st449o2_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p484 : ((3487275578709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 483, stT449o2 (i+1)) + stT449o2 484 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 483
    simpa using h
  have hprev := st449o2_p483
  have hstep := st449o2_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p485 : ((3714295642707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 484, stT449o2 (i+1)) + stT449o2 485 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 484
    simpa using h
  have hprev := st449o2_p484
  have hstep := st449o2_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p486 : ((7832988698613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 485, stT449o2 (i+1)) + stT449o2 486 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 485
    simpa using h
  have hprev := st449o2_p485
  have hstep := st449o2_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p487 : ((2025833566389/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 486, stT449o2 (i+1)) + stT449o2 487 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 486
    simpa using h
  have hprev := st449o2_p486
  have hstep := st449o2_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p488 : ((818382177199/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 487, stT449o2 (i+1)) + stT449o2 488 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 487
    simpa using h
  have hprev := st449o2_p487
  have hstep := st449o2_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p489 : ((4029251158711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 488, stT449o2 (i+1)) + stT449o2 489 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 488
    simpa using h
  have hprev := st449o2_p488
  have hstep := st449o2_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p490 : ((775407523541/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 489, stT449o2 (i+1)) + stT449o2 490 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 489
    simpa using h
  have hprev := st449o2_p489
  have hstep := st449o2_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p491 : ((733390698259/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 490, stT449o2 (i+1)) + stT449o2 491 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 490
    simpa using h
  have hprev := st449o2_p490
  have hstep := st449o2_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p492 : ((1376920693817/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 491, stT449o2 (i+1)) + stT449o2 492 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 491
    simpa using h
  have hprev := st449o2_p491
  have hstep := st449o2_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p493 : ((6498029619589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 492, stT449o2 (i+1)) + stT449o2 493 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 492
    simpa using h
  have hprev := st449o2_p492
  have hstep := st449o2_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p494 : ((6252575122411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 493, stT449o2 (i+1)) + stT449o2 494 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 493
    simpa using h
  have hprev := st449o2_p493
  have hstep := st449o2_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p495 : ((1549351773341/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 494, stT449o2 (i+1)) + stT449o2 495 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 494
    simpa using h
  have hprev := st449o2_p494
  have hstep := st449o2_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p496 : ((6342920083313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 495, stT449o2 (i+1)) + stT449o2 496 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 495
    simpa using h
  have hprev := st449o2_p495
  have hstep := st449o2_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p497 : ((332953899363/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 496, stT449o2 (i+1)) + stT449o2 497 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 496
    simpa using h
  have hprev := st449o2_p496
  have hstep := st449o2_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p498 : ((708191503137/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 497, stT449o2 (i+1)) + stT449o2 498 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 497
    simpa using h
  have hprev := st449o2_p497
  have hstep := st449o2_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p499 : ((7526696228157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 498, stT449o2 (i+1)) + stT449o2 499 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 498
    simpa using h
  have hprev := st449o2_p498
  have hstep := st449o2_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_p500 : ((3952491709479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT449o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT449o2 (i+1))
      = (∑ i ∈ Finset.range 499, stT449o2 (i+1)) + stT449o2 500 := by
    have h := Finset.sum_range_succ (fun i => stT449o2 (i+1)) 499
    simpa using h
  have hprev := st449o2_p499
  have hstep := st449o2_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st449o2_s500 :
    |Real.sin (((449 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))
      - ((533299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log ((500 : ℕ)) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((500 : ℕ)) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact sinMulShift_eval (r := 703119/5000000) (δ := 2279/200000000) (ψ := -125063/500000) 449 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 449/2`** (evaluated boundary). -/
theorem station_449o2_sign : 0 < hardyG (((((449:ℕ)):ℝ)/2)) := by
  have hcore := phase_station_lower_half_eval 449 500 (by norm_num) (by norm_num)
    ((-125063/500000 : ℚ) : ℝ)
  have hchain := st449o2_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT449o2 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((449 : ℕ) : ℝ) * (Real.log ((i+1 : ℕ)) / 2)
              - ((-125063/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st449o2_c500
  have hsinb := abs_le.mp st449o2_s500
  have hbdy_lo : ((-26868581119273/504005000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((449 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ))) / 2
          - ((((449:ℕ)):ℝ)/2)
            * Real.sin (((449 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-125063/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((449:ℕ)):ℝ)/2) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((449:ℝ) * (Real.log (500:ℝ) / 2) - ((-125063/500000 : ℚ) : ℝ))) / 2
        - ((449:ℝ)/2) * Real.sin ((449:ℝ) * (Real.log (500:ℝ) / 2) - ((-125063/500000 : ℚ) : ℝ))
        ≥ ((-120159839/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((449:ℝ)/2) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-120159839/1000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-120159839/1000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-120159839/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((449:ℕ)):ℝ)/2)+1) * (((((449:ℕ)):ℝ)/2)+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((16167971887921/40000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((3952491709479/5000000000000 : ℚ) : ℝ) + ((-26868581119273/504005000000000 : ℚ) : ℝ)
      - ((16167971887921/40000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-125063/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line (((((449:ℕ)):ℝ)/2)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-125063/500000 : ℚ) : ℝ)
        * (riemannZeta (line (((((449:ℕ)):ℝ)/2)))).re
      - Real.sin ((-125063/500000 : ℚ) : ℝ)
        * (riemannZeta (line (((((449:ℕ)):ℝ)/2)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((((449:ℕ)):ℝ)/2))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((((449:ℕ)):ℝ)/2))
      = ((((((449:ℕ)):ℝ)/2)) * (Real.log (((((449:ℕ)):ℝ)/2)) - Real.log 2
          - Real.log Real.pi) - (((((449:ℕ)):ℝ)/2))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM : ((13534689/2500000 : ℚ) : ℝ) ≤ Real.log (((((449:ℕ)):ℝ)/2))
      ∧ Real.log (((((449:ℕ)):ℝ)/2)) ≤ ((27069379/5000000 : ℚ) : ℝ) := by
    have hsplit : Real.log (((((449:ℕ)):ℝ)/2))
        = Real.log ((((449:ℕ)):ℝ)) - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    have hM := log_br_449
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
  have hθwin : |(((-125063/500000 : ℚ) : ℝ) + ((46:ℤ)) * (2*Real.pi)) - theta (((((449:ℕ)):ℝ)/2))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((((449:ℕ)):ℝ)/2)))
    (φ := ((-125063/500000 : ℚ) : ℝ) + ((46:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-125063/500000 : ℚ)) : ℝ) 46).1,
    (cos_sin_shift (((-125063/500000 : ℚ)) : ℝ) 46).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_449o2_sign
end AxiomAudit
