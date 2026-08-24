import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationHalfEval

/-!
# Station `t = 385/2` (rung-199.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT385o2 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((385 : ℕ) : ℝ) * (Real.log ((n : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))

theorem st385o2_c1 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((960701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((0 : ℚ) : ℝ) ≤ Real.log ((1 : ℕ)) / 2 := by
    have h := (log_br_1).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((1 : ℕ)) / 2 ≤ ((0 : ℚ) : ℝ) := by
    have h := (log_br_1).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -351601/5000000) (δ := 201/1000000000) (ψ := 281281/1000000) 385 0
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t1 : ((960651/1000000 : ℚ) : ℝ) ≤ stT385o2 1 := by
  have hc : ((960651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((960651/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((960651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c2 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((359883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log ((2 : ℕ)) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((2 : ℕ)) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 601327/2000000) (δ := 4851/500000000) (ψ := 281281/1000000) 385 21
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t2 : ((2544403251811/10000000000000 : ℚ) : ℝ) ≤ stT385o2 2 := by
  have hc : ((359833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2544403251811/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((359833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c3 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-755179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log ((3 : ℕ)) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((3 : ℕ)) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -758351/1250000) (δ := 4873/500000000) (ψ := 281281/1000000) 385 34
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t3 : ((-4360316897187/10000000000000 : ℚ) : ℝ) ≤ stT385o2 3 := by
  have hc : ((-755229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4360316897187/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-755229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c4 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-112283/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log ((4 : ℕ)) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((4 : ℕ)) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 419781/625000) (δ := 97/10000000) (ψ := 281281/1000000) 385 42
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t4 : ((-2245785449157/5000000000000 : ℚ) : ℝ) ≤ stT385o2 4 := by
  have hc : ((-449157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2245785449157/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-449157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c5 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-22133/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log ((5 : ℕ)) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((5 : ℕ)) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4148611/10000000) (δ := 9703/1000000000) (ψ := 281281/1000000) 385 49
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t5 : ((-24759421947/625000000000 : ℚ) : ℝ) ≤ stT385o2 5 := by
  have hc : ((-44291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24759421947/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-44291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c6 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((293771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log ((6 : ℕ)) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((6 : ℕ)) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2356947/10000000) (δ := 9657/1000000000) (ψ := 281281/1000000) 385 55
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t6 : ((299803189393/1250000000000 : ℚ) : ℝ) ≤ stT385o2 6 := by
  have hc : ((146873/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((299803189393/1250000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((146873/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c7 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-448713/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log ((7 : ℕ)) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((7 : ℕ)) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6711739/10000000) (δ := 9671/1000000000) (ψ := 281281/1000000) 385 60
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t7 : ((-169607033801/500000000000 : ℚ) : ℝ) ≤ stT385o2 7 := by
  have hc : ((-224369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169607033801/500000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-224369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c8 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-515719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log ((8 : ℕ)) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((8 : ℕ)) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2640803/5000000) (δ := 4871/500000000) (ψ := 281281/1000000) 385 64
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t8 : ((-911759417823/5000000000000 : ℚ) : ℝ) ≤ stT385o2 8 := by
  have hc : ((-515769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-911759417823/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-515769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c9 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-69887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log ((9 : ℕ)) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((9 : ℕ)) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4277573/10000000) (δ := 243/25000000) (ψ := 281281/1000000) 385 67
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t9 : ((-14565002913/312500000000 : ℚ) : ℝ) ≤ stT385o2 9 := by
  have hc : ((-8739/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14565002913/312500000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-8739/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c10 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-499999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log ((10 : ℕ)) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((10 : ℕ)) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7849539/10000000) (δ := 9711/1000000000) (ψ := 281281/1000000) 385 71
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t10 : ((-98825930917/312500000000 : ℚ) : ℝ) ≤ stT385o2 10 := by
  have hc : ((-62503/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98825930917/312500000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-62503/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c11 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-877311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log ((11 : ℕ)) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((11 : ℕ)) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 825321/1250000) (δ := 9627/1000000000) (ψ := 281281/1000000) 385 73
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t11 : ((-1322671717077/5000000000000 : ℚ) : ℝ) ≤ stT385o2 11 := by
  have hc : ((-877361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1322671717077/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-877361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c12 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((857109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log ((12 : ℕ)) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((12 : ℕ)) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 676457/5000000) (δ := 4903/500000000) (ψ := 281281/1000000) 385 76
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t12 : ((2474115925309/10000000000000 : ℚ) : ℝ) ≤ stT385o2 12 := by
  have hc : ((857059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2474115925309/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((857059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c13 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-970999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log ((13 : ℕ)) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((13 : ℕ)) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3625213/5000000) (δ := 4817/500000000) (ψ := 281281/1000000) 385 79
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t13 : ((-2693205372549/10000000000000 : ℚ) : ℝ) ≤ stT385o2 13 := by
  have hc : ((-971049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2693205372549/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-971049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c14 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((180829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log ((14 : ℕ)) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((14 : ℕ)) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1500939/5000000) (δ := 491/50000000) (ψ := 281281/1000000) 385 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t14 : ((30201183753/312500000000 : ℚ) : ℝ) ≤ stT385o2 14 := by
  have hc : ((45201/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30201183753/312500000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((45201/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c15 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((442107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log ((15 : ℕ)) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((15 : ℕ)) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1214971/10000000) (δ := 1207/125000000) (ψ := 281281/1000000) 385 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t15 : ((142681302377/625000000000 : ℚ) : ℝ) ≤ stT385o2 15 := by
  have hc : ((221041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142681302377/625000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((221041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c16 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((404397/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log ((16 : ℕ)) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((16 : ℕ)) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -49117/312500) (δ := 4881/500000000) (ψ := 281281/1000000) 385 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t16 : ((101093/500000 : ℚ) : ℝ) ≤ stT385o2 16 := by
  have hc : ((101093/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101093/500000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((101093/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c17 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((45947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log ((17 : ℕ)) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((17 : ℕ)) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1906041/5000000) (δ := 2419/250000000) (ψ := 281281/1000000) 385 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t17 : ((27829141083/2500000000000 : ℚ) : ℝ) ≤ stT385o2 17 := by
  have hc : ((45897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27829141083/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((45897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c18 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-62411/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log ((18 : ℕ)) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((18 : ℕ)) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7720529/10000000) (δ := 9763/1000000000) (ψ := 281281/1000000) 385 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t18 : ((-1176892225199/5000000000000 : ℚ) : ℝ) ≤ stT385o2 18 := by
  have hc : ((-499313/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1176892225199/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-499313/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c19 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((254601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log ((19 : ℕ)) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((19 : ℕ)) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 647837/2500000) (δ := 1931/200000000) (ψ := 281281/1000000) 385 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t19 : ((36502332027/312500000000 : ℚ) : ℝ) ≤ stT385o2 19 := by
  have hc : ((15911/31250 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36502332027/312500000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((15911/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c20 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-21243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log ((20 : ℕ)) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((20 : ℕ)) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2069839/5000000) (δ := 9691/1000000000) (ψ := 281281/1000000) 385 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t20 : ((-23764371687/1250000000000 : ℚ) : ℝ) ≤ stT385o2 20 := by
  have hc : ((-42511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23764371687/1250000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-42511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c21 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((117467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log ((21 : ℕ)) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((21 : ℕ)) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3632643/10000000) (δ := 9769/1000000000) (ψ := 281281/1000000) 385 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t21 : ((128112397113/5000000000000 : ℚ) : ℝ) ≤ stT385o2 21 := by
  have hc : ((117417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128112397113/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((117417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c22 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-554213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log ((22 : ℕ)) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((22 : ℕ)) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2697767/5000000) (δ := 9669/1000000000) (ψ := 281281/1000000) 385 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t22 : ((-147711643763/1250000000000 : ℚ) : ℝ) ≤ stT385o2 22 := by
  have hc : ((-554263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147711643763/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-554263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c23 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((993329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log ((23 : ℕ)) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((23 : ℕ)) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 72233/2500000) (δ := 9791/1000000000) (ψ := 281281/1000000) 385 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t23 : ((258891218397/1250000000000 : ℚ) : ℝ) ≤ stT385o2 23 := by
  have hc : ((993279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258891218397/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((993279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c24 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-219423/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log ((24 : ℕ)) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((24 : ℕ)) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 632847/1250000) (δ := 4849/500000000) (ψ := 281281/1000000) 385 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t24 : ((-27996654651/312500000000 : ℚ) : ℝ) ≤ stT385o2 24 := by
  have hc : ((-27431/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27996654651/312500000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-27431/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c25 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-56043/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log ((25 : ℕ)) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((25 : ℕ)) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6707563/10000000) (δ := 607/62500000) (ψ := 281281/1000000) 385 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t25 : ((-896738448369/5000000000000 : ℚ) : ℝ) ≤ stT385o2 25 := by
  have hc : ((-448369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-896738448369/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-448369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c26 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((38489/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log ((26 : ℕ)) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((26 : ℕ)) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -708113/2000000) (δ := 1223/125000000) (ψ := 281281/1000000) 385 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t26 : ((150917222433/5000000000000 : ℚ) : ℝ) ≤ stT385o2 26 := by
  have hc : ((76953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150917222433/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((76953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c27 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((907121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log ((27 : ℕ)) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((27 : ℕ)) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1086009/10000000) (δ := 4913/500000000) (ψ := 281281/1000000) 385 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t27 : ((3491316279/20000000000 : ℚ) : ℝ) ≤ stT385o2 27 := by
  have hc : ((907071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3491316279/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((907071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c28 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((120021/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log ((28 : ℕ)) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((28 : ℕ)) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 44249/625000) (δ := 2421/250000000) (ψ := 281281/1000000) 385 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t28 : ((453613029749/2500000000000 : ℚ) : ℝ) ≤ stT385o2 28 := by
  have hc : ((480059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((453613029749/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((480059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c29 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((364107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log ((29 : ℕ)) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((29 : ℕ)) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1887709/10000000) (δ := 9741/1000000000) (ψ := 281281/1000000) 385 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t29 : ((338041581073/2500000000000 : ℚ) : ℝ) ≤ stT385o2 29 := by
  have hc : ((182041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((338041581073/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((182041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c30 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((542037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log ((30 : ℕ)) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((30 : ℕ)) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1247421/5000000) (δ := 1951/200000000) (ψ := 281281/1000000) 385 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t30 : ((989527887367/10000000000000 : ℚ) : ℝ) ≤ stT385o2 30 := by
  have hc : ((541987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((989527887367/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((541987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c31 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((517553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log ((31 : ℕ)) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((31 : ℕ)) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1283509/5000000) (δ := 4899/500000000) (ψ := 281281/1000000) 385 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t31 : ((929462815659/10000000000000 : ℚ) : ℝ) ≤ stT385o2 31 := by
  have hc : ((517503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((929462815659/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((517503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c32 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((20501/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log ((32 : ℕ)) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((32 : ℕ)) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2138117/10000000) (δ := 241/25000000) (ψ := 281281/1000000) 385 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t32 : ((289905669053/2500000000000 : ℚ) : ℝ) ≤ stT385o2 32 := by
  have hc : ((327991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((289905669053/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((327991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c33 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((439843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log ((33 : ℕ)) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((33 : ℕ)) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 619493/5000000) (δ := 9733/1000000000) (ψ := 281281/1000000) 385 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t33 : ((47851538673/312500000000 : ℚ) : ℝ) ≤ stT385o2 33 := by
  have hc : ((219909/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47851538673/312500000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((219909/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c34 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((249791/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log ((34 : ℕ)) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((34 : ℕ)) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -102221/10000000) (δ := 4863/500000000) (ψ := 281281/1000000) 385 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t34 : ((171346552329/1000000000000 : ℚ) : ℝ) ≤ stT385o2 34 := by
  have hc : ((499557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171346552329/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((499557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c35 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((735779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log ((35 : ℕ)) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((35 : ℕ)) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -37199/200000) (δ := 9769/1000000000) (ψ := 281281/1000000) 385 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t35 : ((310902153633/2500000000000 : ℚ) : ℝ) ≤ stT385o2 35 := by
  have hc : ((735729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310902153633/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((735729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c36 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-4183/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log ((36 : ℕ)) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((36 : ℕ)) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4010667/10000000) (δ := 9741/1000000000) (ψ := 281281/1000000) 385 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t36 : ((-27928338919/5000000000000 : ℚ) : ℝ) ≤ stT385o2 36 := by
  have hc : ((-16757/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27928338919/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-16757/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c37 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-863591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log ((37 : ℕ)) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((37 : ℕ)) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3266431/5000000) (δ := 1941/200000000) (ψ := 281281/1000000) 385 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t37 : ((-141981716759/1000000000000 : ℚ) : ℝ) ≤ stT385o2 37 := by
  have hc : ((-863641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141981716759/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-863641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c38 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-406617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log ((38 : ℕ)) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((38 : ℕ)) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6301209/10000000) (δ := 1961/200000000) (ψ := 281281/1000000) 385 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t38 : ((-65966075203/500000000000 : ℚ) : ℝ) ≤ stT385o2 38 := by
  have hc : ((-203321/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65966075203/500000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-203321/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c39 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((163541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log ((39 : ℕ)) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((39 : ℕ)) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 773489/2500000) (δ := 4903/500000000) (ψ := 281281/1000000) 385 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t39 : ((65458765999/1250000000000 : ℚ) : ℝ) ≤ stT385o2 39 := by
  have hc : ((40879/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65458765999/1250000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((40879/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c40 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((985257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log ((40 : ℕ)) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((40 : ℕ)) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -53727/1250000) (δ := 9813/1000000000) (ψ := 281281/1000000) 385 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t40 : ((778874112783/5000000000000 : ℚ) : ℝ) ≤ stT385o2 40 := by
  have hc : ((985207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((778874112783/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((985207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c41 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-16327/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log ((41 : ℕ)) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((41 : ℕ)) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2127233/5000000) (δ := 9633/1000000000) (ψ := 281281/1000000) 385 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t41 : ((-51016514377/2500000000000 : ℚ) : ℝ) ≤ stT385o2 41 := by
  have hc : ((-65333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51016514377/2500000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-65333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c42 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-122393/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log ((42 : ℕ)) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((42 : ℕ)) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 917813/1250000) (δ := 9633/1000000000) (ψ := 281281/1000000) 385 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t42 : ((-377732408649/2500000000000 : ℚ) : ℝ) ≤ stT385o2 42 := by
  have hc : ((-489597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-377732408649/2500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-489597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c43 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((23609/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log ((43 : ℕ)) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((43 : ℕ)) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1479297/5000000) (δ := 9677/1000000000) (ψ := 281281/1000000) 385 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t43 : ((57597768459/1000000000000 : ℚ) : ℝ) ≤ stT385o2 43 := by
  have hc : ((188847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57597768459/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((188847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c44 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((781163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log ((44 : ℕ)) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((44 : ℕ)) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1685673/10000000) (δ := 9819/1000000000) (ψ := 281281/1000000) 385 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t44 : ((294392897457/2500000000000 : ℚ) : ℝ) ≤ stT385o2 44 := by
  have hc : ((781113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((294392897457/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((781113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c45 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-87267/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log ((45 : ℕ)) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((45 : ℕ)) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6578601/10000000) (δ := 9711/1000000000) (ψ := 281281/1000000) 385 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t45 : ((-2032772151/15625000000 : ℚ) : ℝ) ≤ stT385o2 45 := by
  have hc : ((-10909/12500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2032772151/15625000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-10909/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c46 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-14349/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log ((46 : ℕ)) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((46 : ℕ)) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 799749/2000000) (δ := 2423/250000000) (ψ := 281281/1000000) 385 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t46 : ((-529832827/125000000000 : ℚ) : ℝ) ≤ stT385o2 46 := by
  have hc : ((-7187/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-529832827/125000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-7187/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c47 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((213947/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log ((47 : ℕ)) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((47 : ℕ)) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -84957/625000) (δ := 2451/250000000) (ψ := 281281/1000000) 385 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t47 : ((624110688981/5000000000000 : ℚ) : ℝ) ≤ stT385o2 47 := by
  have hc : ((427869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((624110688981/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((427869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c48 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-466621/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log ((48 : ℕ)) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((48 : ℕ)) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3467663/5000000) (δ := 1207/125000000) (ψ := 281281/1000000) 385 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t48 : ((-21048301153/156250000000 : ℚ) : ℝ) ≤ stT385o2 48 := by
  have hc : ((-233323/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21048301153/156250000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-233323/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c49 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((45869/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log ((49 : ℕ)) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((49 : ℕ)) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 186729/625000) (δ := 1207/125000000) (ψ := 281281/1000000) 385 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t49 : ((262072778521/5000000000000 : ℚ) : ℝ) ≤ stT385o2 49 := by
  have hc : ((183451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((262072778521/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((183451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c50 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((181607/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log ((50 : ℕ)) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((50 : ℕ)) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1498851/5000000) (δ := 969/100000000) (ψ := 281281/1000000) 385 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t50 : ((128397812483/2500000000000 : ℚ) : ℝ) ≤ stT385o2 50 := by
  have hc : ((90791/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128397812483/2500000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((90791/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c51 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-863477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log ((51 : ℕ)) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((51 : ℕ)) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6532299/10000000) (δ := 979/100000000) (ψ := 281281/1000000) 385 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t51 : ((-1209180451087/10000000000000 : ℚ) : ℝ) ≤ stT385o2 51 := by
  have hc : ((-863527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1209180451087/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-863527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c52 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((249427/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log ((52 : ℕ)) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((52 : ℕ)) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 169297/10000000) (δ := 243/25000000) (ψ := 281281/1000000) 385 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t52 : ((2767004463/20000000000 : ℚ) : ℝ) ≤ stT385o2 52 := by
  have hc : ((498829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2767004463/20000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((498829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c53 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-829321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log ((53 : ℕ)) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((53 : ℕ)) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -159293/250000) (δ := 9727/1000000000) (ψ := 281281/1000000) 385 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t53 : ((-569614490913/5000000000000 : ℚ) : ℝ) ≤ stT385o2 53 := by
  have hc : ((-829371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-569614490913/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-829371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c54 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((497969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log ((54 : ℕ)) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((54 : ℕ)) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2623853/10000000) (δ := 9677/1000000000) (ψ := 281281/1000000) 385 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t54 : ((677581619013/10000000000000 : ℚ) : ℝ) ≤ stT385o2 54 := by
  have hc : ((497919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((677581619013/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((497919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c55 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-5211/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log ((55 : ℕ)) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((55 : ℕ)) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2126803/5000000) (δ := 1927/200000000) (ψ := 281281/1000000) 385 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t55 : ((-17573023/1000000000 : ℚ) : ℝ) ≤ stT385o2 55 := by
  have hc : ((-5213/40000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17573023/1000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-5213/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c56 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-24383/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log ((56 : ℕ)) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((56 : ℕ)) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4417797/10000000) (δ := 2417/250000000) (ψ := 281281/1000000) 385 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t56 : ((-130366101999/5000000000000 : ℚ) : ℝ) ≤ stT385o2 56 := by
  have hc : ((-97557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130366101999/5000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-97557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c57 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((111413/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log ((57 : ℕ)) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((57 : ℕ)) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1386117/5000000) (δ := 9761/1000000000) (ψ := 281281/1000000) 385 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t57 : ((73776763533/1250000000000 : ℚ) : ℝ) ≤ stT385o2 57 := by
  have hc : ((222801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73776763533/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((222801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c58 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-619599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log ((58 : ℕ)) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((58 : ℕ)) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 559757/1000000) (δ := 9661/1000000000) (ψ := 281281/1000000) 385 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t58 : ((-162727882837/2000000000000 : ℚ) : ℝ) ≤ stT385o2 58 := by
  have hc : ((-619649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162727882837/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-619649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c59 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((729309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log ((59 : ℕ)) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((59 : ℕ)) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1883713/10000000) (δ := 9699/1000000000) (ψ := 281281/1000000) 385 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t59 : ((949414270251/10000000000000 : ℚ) : ℝ) ≤ stT385o2 59 := by
  have hc : ((729259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((949414270251/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((729259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c60 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-790169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log ((60 : ℕ)) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((60 : ℕ)) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 193897/312500) (δ := 9749/1000000000) (ψ := 281281/1000000) 385 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t60 : ((-204033755581/2000000000000 : ℚ) : ℝ) ≤ stT385o2 60 := by
  have hc : ((-790219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204033755581/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-790219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c61 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((814219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log ((61 : ℕ)) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((61 : ℕ)) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -774267/5000000) (δ := 9647/1000000000) (ψ := 281281/1000000) 385 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t61 : ((65152245887/625000000000 : ℚ) : ℝ) ≤ stT385o2 61 := by
  have hc : ((814169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65152245887/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((814169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c62 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-807521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log ((62 : ℕ)) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((62 : ℕ)) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 196151/312500) (δ := 2439/250000000) (ψ := 281281/1000000) 385 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t62 : ((-512808392571/5000000000000 : ℚ) : ℝ) ≤ stT385o2 62 := by
  have hc : ((-807571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512808392571/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-807571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c63 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((192433/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log ((63 : ℕ)) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((63 : ℕ)) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1730939/10000000) (δ := 9663/1000000000) (ψ := 281281/1000000) 385 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t63 : ((484853863921/5000000000000 : ℚ) : ℝ) ≤ stT385o2 63 := by
  have hc : ((384841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((484853863921/5000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((384841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c64 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-86871/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log ((64 : ℕ)) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((64 : ℕ)) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 584793/1000000) (δ := 487/50000000) (ψ := 281281/1000000) 385 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t64 : ((-434386597509/5000000000000 : ℚ) : ℝ) ≤ stT385o2 64 := by
  have hc : ((-347509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-434386597509/5000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-347509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c65 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((573967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log ((65 : ℕ)) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((65 : ℕ)) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2398637/10000000) (δ := 9733/1000000000) (ψ := 281281/1000000) 385 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t65 : ((711856229199/10000000000000 : ℚ) : ℝ) ≤ stT385o2 65 := by
  have hc : ((573917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((711856229199/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((573917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c66 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-24841/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log ((66 : ℕ)) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((66 : ℕ)) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 309303/625000) (δ := 977/100000000) (ψ := 281281/1000000) 385 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t66 : ((-48929609799/1000000000000 : ℚ) : ℝ) ≤ stT385o2 66 := by
  have hc : ((-198753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48929609799/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-198753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c67 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((161239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log ((67 : ℕ)) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((67 : ℕ)) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1761063/5000000) (δ := 19/1953125) (ψ := 281281/1000000) 385 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t67 : ((98461817083/5000000000000 : ℚ) : ℝ) ≤ stT385o2 67 := by
  have hc : ((161189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98461817083/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((161189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c68 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((127393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log ((68 : ℕ)) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((68 : ℕ)) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3607641/10000000) (δ := 4889/500000000) (ψ := 281281/1000000) 385 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t68 : ((77213027277/5000000000000 : ℚ) : ℝ) ≤ stT385o2 68 := by
  have hc : ((127343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77213027277/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((127343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c69 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-443109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log ((69 : ℕ)) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((69 : ℕ)) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -101493/200000) (δ := 1937/200000000) (ψ := 281281/1000000) 385 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t69 : ((-533500950581/10000000000000 : ℚ) : ℝ) ≤ stT385o2 69 := by
  have hc : ((-443159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-533500950581/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-443159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c70 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((184623/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log ((70 : ℕ)) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((70 : ℕ)) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 231239/1250000) (δ := 1947/200000000) (ψ := 281281/1000000) 385 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t70 : ((110325819347/1250000000000 : ℚ) : ℝ) ≤ stT385o2 70 := by
  have hc : ((369221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110325819347/1250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((369221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c71 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-236599/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log ((71 : ℕ)) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((71 : ℕ)) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7031713/10000000) (δ := 9711/1000000000) (ψ := 281281/1000000) 385 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t71 : ((-280806269193/2500000000000 : ℚ) : ℝ) ≤ stT385o2 71 := by
  have hc : ((-473223/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-280806269193/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-473223/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c72 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((99277/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log ((72 : ℕ)) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((72 : ℕ)) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -150403/5000000) (δ := 9661/1000000000) (ψ := 281281/1000000) 385 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t72 : ((14624142999/125000000000 : ℚ) : ℝ) ≤ stT385o2 72 := by
  have hc : ((12409/12500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14624142999/125000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((12409/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c73 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-821531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log ((73 : ℕ)) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((73 : ℕ)) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 316861/500000) (δ := 4871/500000000) (ψ := 281281/1000000) 385 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t73 : ((-240397065343/2500000000000 : ℚ) : ℝ) ≤ stT385o2 73 := by
  have hc : ((-821581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240397065343/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-821581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c74 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((85473/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log ((74 : ℕ)) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((74 : ℕ)) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2823049/10000000) (δ := 2451/250000000) (ψ := 281281/1000000) 385 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t74 : ((24837171597/500000000000 : ℚ) : ℝ) ≤ stT385o2 74 := by
  have hc : ((85463/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24837171597/500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((85463/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c75 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((115809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log ((75 : ℕ)) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((75 : ℕ)) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1818409/5000000) (δ := 4877/500000000) (ψ := 281281/1000000) 385 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t75 : ((1336669173/100000000000 : ℚ) : ℝ) ≤ stT385o2 75 := by
  have hc : ((115759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1336669173/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((115759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c76 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-325143/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log ((76 : ℕ)) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((76 : ℕ)) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1424223/2500000) (δ := 4903/500000000) (ψ := 281281/1000000) 385 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t76 : ((-23312086517/312500000000 : ℚ) : ℝ) ≤ stT385o2 76 := by
  have hc : ((-20323/31250 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23312086517/312500000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-20323/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c77 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((9719/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log ((77 : ℕ)) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((77 : ℕ)) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 74257/1250000) (δ := 2439/250000000) (ψ := 281281/1000000) 385 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t77 : ((4430100477/40000000000 : ℚ) : ℝ) ≤ stT385o2 77 := by
  have hc : ((19437/20000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4430100477/40000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((19437/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c78 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-456531/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log ((78 : ℕ)) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((78 : ℕ)) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6803817/10000000) (δ := 1207/125000000) (ψ := 281281/1000000) 385 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t78 : ((-64618539321/625000000000 : ℚ) : ℝ) ≤ stT385o2 78 := by
  have hc : ((-114139/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64618539321/625000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-114139/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c79 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((222599/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log ((79 : ℕ)) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((79 : ℕ)) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2773503/10000000) (δ := 9789/1000000000) (ψ := 281281/1000000) 385 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t79 : ((125207556969/2500000000000 : ℚ) : ℝ) ≤ stT385o2 79 := by
  have hc : ((111287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125207556969/2500000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((111287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c80 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((2559/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log ((80 : ℕ)) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((80 : ℕ)) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 656009/2000000) (δ := 151/15625000) (ψ := 281281/1000000) 385 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t80 : ((5720974861/200000000000 : ℚ) : ℝ) ≤ stT385o2 80 := by
  have hc : ((5117/20000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5720974861/200000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((5117/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c81 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-846321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log ((81 : ℕ)) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((81 : ℕ)) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -644959/1000000) (δ := 9721/1000000000) (ψ := 281281/1000000) 385 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t81 : ((-117551621819/1250000000000 : ℚ) : ℝ) ≤ stT385o2 81 := by
  have hc : ((-846371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117551621819/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-846371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c82 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((488183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log ((82 : ℕ)) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((82 : ℕ)) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -108921/2000000) (δ := 4891/500000000) (ψ := 281281/1000000) 385 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t82 : ((53908020177/500000000000 : ℚ) : ℝ) ≤ stT385o2 82 := by
  have hc : ((244079/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53908020177/500000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((244079/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c83 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-129547/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log ((83 : ℕ)) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((83 : ℕ)) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5288819/10000000) (δ := 4841/500000000) (ψ := 281281/1000000) 385 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t83 : ((-284420156517/5000000000000 : ℚ) : ℝ) ≤ stT385o2 83 := by
  have hc : ((-259119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284420156517/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-259119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c84 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-17959/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log ((84 : ℕ)) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((84 : ℕ)) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2327811/5000000) (δ := 771/40000000) (ψ := 281281/1000000) 385 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t84 : ((-15678635973/500000000000 : ℚ) : ℝ) ≤ stT385o2 84 := by
  have hc : ((-143697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15678635973/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-143697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c85 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((22869/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log ((85 : ℕ)) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((85 : ℕ)) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1039707/10000000) (δ := 387/40000000) (ψ := 281281/1000000) 385 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t85 : ((24803550773/250000000000 : ℚ) : ℝ) ≤ stT385o2 85 := by
  have hc : ((91471/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24803550773/250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((91471/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c86 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-177929/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log ((86 : ℕ)) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((86 : ℕ)) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6668407/10000000) (δ := 387/40000000) (ψ := 281281/1000000) 385 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t86 : ((-23984575749/250000000000 : ℚ) : ℝ) ≤ stT385o2 86 := by
  have hc : ((-177939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23984575749/250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-177939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c87 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((179469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log ((87 : ℕ)) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((87 : ℕ)) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3475873/10000000) (δ := 1927/200000000) (ψ := 281281/1000000) 385 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t87 : ((12022328933/625000000000 : ℚ) : ℝ) ≤ stT385o2 87 := by
  have hc : ((179419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12022328933/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((179419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c88 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((689733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log ((88 : ℕ)) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((88 : ℕ)) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2024189/10000000) (δ := 1937/200000000) (ψ := 281281/1000000) 385 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t88 : ((735204147049/10000000000000 : ℚ) : ℝ) ≤ stT385o2 88 := by
  have hc : ((689683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((735204147049/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((689683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c89 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-493869/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log ((89 : ℕ)) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((89 : ℕ)) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7462073/10000000) (δ := 4859/500000000) (ψ := 281281/1000000) 385 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t89 : ((-130881663053/1250000000000 : ℚ) : ℝ) ≤ stT385o2 89 := by
  have hc : ((-246947/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130881663053/1250000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-246947/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c90 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((102693/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log ((90 : ℕ)) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((90 : ℕ)) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2868739/10000000) (δ := 153/15625000) (ψ := 281281/1000000) 385 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t90 : ((54117346803/1250000000000 : ℚ) : ℝ) ≤ stT385o2 90 := by
  have hc : ((205361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54117346803/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((205361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c91 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((278677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log ((91 : ℕ)) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((91 : ℕ)) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2449001/10000000) (δ := 4823/250000000) (ψ := 281281/1000000) 385 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t91 : ((18256652073/312500000000 : ℚ) : ℝ) ≤ stT385o2 91 := by
  have hc : ((69663/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18256652073/312500000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((69663/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c92 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-99831/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log ((92 : ℕ)) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((92 : ℕ)) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3854303/5000000) (δ := 9711/1000000000) (ψ := 281281/1000000) 385 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t92 : ((-26021579507/250000000000 : ℚ) : ℝ) ≤ stT385o2 92 := by
  have hc : ((-24959/25000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26021579507/250000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-24959/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c93 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((218451/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log ((93 : ℕ)) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((93 : ℕ)) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2796611/10000000) (δ := 9799/1000000000) (ψ := 281281/1000000) 385 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t93 : ((113248529563/2500000000000 : ℚ) : ℝ) ≤ stT385o2 93 := by
  have hc : ((109213/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113248529563/2500000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((109213/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c94 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((294813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log ((94 : ℕ)) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((94 : ℕ)) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1175251/5000000) (δ := 9749/1000000000) (ψ := 281281/1000000) 385 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t94 : ((76012633437/1250000000000 : ℚ) : ℝ) ≤ stT385o2 94 := by
  have hc : ((73697/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76012633437/1250000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((73697/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c95 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-986527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log ((95 : ℕ)) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((95 : ℕ)) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7443137/10000000) (δ := 4877/500000000) (ψ := 281281/1000000) 385 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t95 : ((-1012207283883/10000000000000 : ℚ) : ℝ) ≤ stT385o2 95 := by
  have hc : ((-986577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1012207283883/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-986577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c96 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((69231/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log ((96 : ℕ)) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((96 : ℕ)) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3225513/10000000) (δ := 303/31250000) (ψ := 281281/1000000) 385 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t96 : ((7064578547/250000000000 : ℚ) : ℝ) ≤ stT385o2 96 := by
  have hc : ((138437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7064578547/250000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((138437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c97 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((761849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log ((97 : ℕ)) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((97 : ℕ)) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 352317/2000000) (δ := 9757/1000000000) (ψ := 281281/1000000) 385 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t97 : ((386744783727/5000000000000 : ℚ) : ℝ) ≤ stT385o2 97 := by
  have hc : ((761799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((386744783727/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((761799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c98 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-894903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log ((98 : ℕ)) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((98 : ℕ)) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 267901/400000) (δ := 4873/500000000) (ψ := 281281/1000000) 385 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t98 : ((-904039457809/10000000000000 : ℚ) : ℝ) ≤ stT385o2 98 := by
  have hc : ((-894953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-904039457809/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-894953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c99 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-78959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log ((99 : ℕ)) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((99 : ℕ)) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -824919/2000000) (δ := 4907/500000000) (ψ := 281281/1000000) 385 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t99 : ((-39703523671/5000000000000 : ℚ) : ℝ) ≤ stT385o2 99 := by
  have hc : ((-79009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39703523671/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-79009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c100 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((191941/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log ((100 : ℕ)) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((100 : ℕ)) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 712111/10000000) (δ := 9789/1000000000) (ψ := 281281/1000000) 385 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t100 : ((191930808069/2000000000000 : ℚ) : ℝ) ≤ stT385o2 100 := by
  have hc : ((191931/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191930808069/2000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((191931/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c101 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-588741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log ((101 : ℕ)) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((101 : ℕ)) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5500741/10000000) (δ := 9789/1000000000) (ψ := 281281/1000000) 385 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t101 : ((-292934709529/5000000000000 : ℚ) : ℝ) ≤ stT385o2 101 := by
  have hc : ((-588791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-292934709529/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-588791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c102 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-577387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log ((102 : ℕ)) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((102 : ℕ)) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2732901/5000000) (δ := 9821/1000000000) (ψ := 281281/1000000) 385 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t102 : ((-142937022669/2500000000000 : ℚ) : ℝ) ≤ stT385o2 102 := by
  have hc : ((-577437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142937022669/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-577437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c103 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((952859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log ((103 : ℕ)) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((103 : ℕ)) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -770679/10000000) (δ := 9771/1000000000) (ψ := 281281/1000000) 385 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t103 : ((938830339161/10000000000000 : ℚ) : ℝ) ≤ stT385o2 103 := by
  have hc : ((952809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((938830339161/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((952809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c104 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((19151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log ((104 : ℕ)) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((104 : ℕ)) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 387911/1000000) (δ := 301/31250000) (ψ := 281281/1000000) 385 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t104 : ((936502929/500000000000 : ℚ) : ℝ) ≤ stT385o2 104 := by
  have hc : ((19101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((936502929/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((19101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c105 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-968371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log ((105 : ℕ)) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((105 : ℕ)) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7223531/10000000) (δ := 4889/500000000) (ψ := 281281/1000000) 385 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t105 : ((-945083022321/10000000000000 : ℚ) : ℝ) ≤ stT385o2 105 := by
  have hc : ((-968421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-945083022321/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-968421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c106 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((60589/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log ((106 : ℕ)) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((106 : ℕ)) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2661907/10000000) (δ := 2407/250000000) (ψ := 281281/1000000) 385 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t106 : ((47074493067/1000000000000 : ℚ) : ℝ) ≤ stT385o2 106 := by
  have hc : ((242331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47074493067/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((242331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c107 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((184149/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log ((107 : ℕ)) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((107 : ℕ)) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 928467/5000000) (δ := 389/40000000) (ψ := 281281/1000000) 385 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t107 : ((22251422933/312500000000 : ℚ) : ℝ) ≤ stT385o2 107 := by
  have hc : ((368273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22251422933/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((368273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c108 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-820731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log ((108 : ℕ)) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((108 : ℕ)) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3166857/5000000) (δ := 389/40000000) (ψ := 281281/1000000) 385 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t108 : ((-789797338031/10000000000000 : ℚ) : ℝ) ≤ stT385o2 108 := by
  have hc : ((-820781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-789797338031/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-820781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c109 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-63/160 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log ((109 : ℕ)) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((109 : ℕ)) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -123469/250000) (δ := 1947/200000000) (ψ := 281281/1000000) 385 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t109 : ((-1885961363/50000000000 : ℚ) : ℝ) ≤ stT385o2 109 := by
  have hc : ((-1969/5000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1885961363/50000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-1969/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c110 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((24411/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log ((110 : ℕ)) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((110 : ℕ)) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -108749/2000000) (δ := 1221/125000000) (ψ := 281281/1000000) 385 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t110 : ((46547538109/500000000000 : ℚ) : ℝ) ≤ stT385o2 110 := by
  have hc : ((97639/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46547538109/500000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((97639/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c111 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((11543/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log ((111 : ℕ)) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((111 : ℕ)) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 11911/31250) (δ := 1947/200000000) (ψ := 281281/1000000) 385 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t111 : ((21888509577/5000000000000 : ℚ) : ℝ) ≤ stT385o2 111 := by
  have hc : ((23061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21888509577/5000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((23061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c112 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-497007/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log ((112 : ℕ)) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((112 : ℕ)) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1516061/2000000) (δ := 971/100000000) (ψ := 281281/1000000) 385 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t112 : ((-3669152353/39062500000 : ℚ) : ℝ) ≤ stT385o2 112 := by
  have hc : ((-62129/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3669152353/39062500000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-62129/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c113 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((247217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log ((113 : ℕ)) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((113 : ℕ)) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1651237/5000000) (δ := 981/100000000) (ψ := 281281/1000000) 385 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t113 : ((2906436753/125000000000 : ℚ) : ℝ) ≤ stT385o2 113 := by
  have hc : ((247167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2906436753/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((247167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c114 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((930489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log ((114 : ℕ)) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((114 : ℕ)) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 234407/2500000) (δ := 9743/1000000000) (ψ := 281281/1000000) 385 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t114 : ((174287042163/2000000000000 : ℚ) : ℝ) ≤ stT385o2 114 := by
  have hc : ((930439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174287042163/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((930439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c115 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-116661/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log ((115 : ℕ)) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((115 : ℕ)) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5140721/10000000) (δ := 9693/1000000000) (ψ := 281281/1000000) 385 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t115 : ((-43519448847/1000000000000 : ℚ) : ℝ) ≤ stT385o2 115 := by
  have hc : ((-233347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43519448847/1000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-233347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c116 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-208929/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log ((116 : ℕ)) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((116 : ℕ)) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -320029/500000) (δ := 9653/1000000000) (ψ := 281281/1000000) 385 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t116 : ((-387994754191/5000000000000 : ℚ) : ℝ) ≤ stT385o2 116 := by
  have hc : ((-417883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-387994754191/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-417883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c117 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((615441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log ((117 : ℕ)) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((117 : ℕ)) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1134813/5000000) (δ := 97/10000000) (ψ := 281281/1000000) 385 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t117 : ((1137857959/20000000000 : ℚ) : ℝ) ≤ stT385o2 117 := by
  have hc : ((615391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1137857959/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((615391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c118 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((186217/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log ((118 : ℕ)) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((118 : ℕ)) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 456537/2500000) (δ := 9703/1000000000) (ψ := 281281/1000000) 385 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t118 : ((171415021383/2500000000000 : ℚ) : ℝ) ≤ stT385o2 118 := by
  have hc : ((372409/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171415021383/2500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((372409/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c119 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-706211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log ((119 : ℕ)) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((119 : ℕ)) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5887321/10000000) (δ := 39/4000000) (ψ := 281281/1000000) 385 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t119 : ((-647428752439/10000000000000 : ℚ) : ℝ) ≤ stT385o2 119 := by
  have hc : ((-706261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-647428752439/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-706261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c120 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-8489/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log ((120 : ℕ)) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((120 : ℕ)) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2896699/5000000) (δ := 9707/1000000000) (ψ := 281281/1000000) 385 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t120 : ((-61999459707/1000000000000 : ℚ) : ℝ) ≤ stT385o2 120 := by
  have hc : ((-67917/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61999459707/1000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-67917/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c121 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((751911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log ((121 : ℕ)) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((121 : ℕ)) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1799601/10000000) (δ := 4873/500000000) (ψ := 281281/1000000) 385 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t121 : ((68350931649/1000000000000 : ℚ) : ℝ) ≤ stT385o2 121 := by
  have hc : ((751861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68350931649/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((751861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c122 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((648997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log ((122 : ℕ)) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((122 : ℕ)) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2161327/10000000) (δ := 2449/250000000) (ψ := 281281/1000000) 385 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t122 : ((587528709079/10000000000000 : ℚ) : ℝ) ≤ stT385o2 122 := by
  have hc : ((648947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((587528709079/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((648947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c123 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-380603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log ((123 : ℕ)) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((123 : ℕ)) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1522479/2500000) (δ := 9807/1000000000) (ψ := 281281/1000000) 385 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t123 : ((-8580021219/125000000000 : ℚ) : ℝ) ≤ stT385o2 123 := by
  have hc : ((-95157/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8580021219/125000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-95157/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c124 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-657663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log ((124 : ℕ)) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((124 : ℕ)) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -572127/1000000) (δ := 4857/500000000) (ψ := 281281/1000000) 385 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t124 : ((-590644032251/10000000000000 : ℚ) : ℝ) ≤ stT385o2 124 := by
  have hc : ((-657713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-590644032251/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-657713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c125 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((736909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log ((125 : ℕ)) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((125 : ℕ)) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -927887/5000000) (δ := 9639/1000000000) (ψ := 281281/1000000) 385 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t125 : ((659066584793/10000000000000 : ℚ) : ℝ) ≤ stT385o2 125 := by
  have hc : ((736859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((659066584793/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((736859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c126 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((70273/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log ((126 : ℕ)) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((126 : ℕ)) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 989461/5000000) (δ := 9739/1000000000) (ψ := 281281/1000000) 385 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t126 : ((1564991329/25000000000 : ℚ) : ℝ) ≤ stT385o2 126 := by
  have hc : ((17567/25000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1564991329/25000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((17567/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c127 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-135227/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log ((127 : ℕ)) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((127 : ℕ)) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1445813/2500000) (δ := 2441/250000000) (ψ := 281281/1000000) 385 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t127 : ((-120003498609/2000000000000 : ℚ) : ℝ) ≤ stT385o2 127 := by
  have hc : ((-135237/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120003498609/2000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-135237/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c128 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-388307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log ((128 : ℕ)) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((128 : ℕ)) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1537543/2500000) (δ := 4891/500000000) (ψ := 281281/1000000) 385 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t128 : ((-21452527593/312500000000 : ℚ) : ℝ) ≤ stT385o2 128 := by
  have hc : ((-97083/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21452527593/312500000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-97083/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c129 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((142971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log ((129 : ℕ)) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((129 : ℕ)) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -601247/2500000) (δ := 4841/500000000) (ψ := 281281/1000000) 385 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t129 : ((5034712453/100000000000 : ℚ) : ℝ) ≤ stT385o2 129 := by
  have hc : ((285917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5034712453/100000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((285917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c130 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((865579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log ((130 : ℕ)) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((130 : ℕ)) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 52449/400000) (δ := 9771/1000000000) (ψ := 281281/1000000) 385 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t130 : ((379559566841/5000000000000 : ℚ) : ℝ) ≤ stT385o2 130 := by
  have hc : ((865529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((379559566841/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((865529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c131 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-415781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log ((131 : ℕ)) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((131 : ℕ)) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 999799/2000000) (δ := 2433/250000000) (ψ := 281281/1000000) 385 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t131 : ((-72662724771/2000000000000 : ℚ) : ℝ) ≤ stT385o2 131 := by
  have hc : ((-415831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72662724771/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-415831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c132 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-948639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log ((132 : ℕ)) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((132 : ℕ)) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3524627/5000000) (δ := 19/1953125) (ψ := 281281/1000000) 385 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t132 : ((-825728470021/10000000000000 : ℚ) : ℝ) ≤ stT385o2 132 := by
  have hc : ((-948689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-825728470021/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-948689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c133 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((5063/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log ((133 : ℕ)) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((133 : ℕ)) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -854291/2500000) (δ := 19/1953125) (ψ := 281281/1000000) 385 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t133 : ((17556355923/1000000000000 : ℚ) : ℝ) ≤ stT385o2 133 := by
  have hc : ((20247/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17556355923/1000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((20247/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c134 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((498591/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log ((134 : ℕ)) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((134 : ℕ)) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 187711/10000000) (δ := 771/40000000) (ψ := 281281/1000000) 385 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t134 : ((53836901661/625000000000 : ℚ) : ℝ) ≤ stT385o2 134 := by
  have hc : ((249283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53836901661/625000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((249283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c135 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((64439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log ((135 : ℕ)) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((135 : ℕ)) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3765781/10000000) (δ := 19/1953125) (ψ := 281281/1000000) 385 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t135 : ((27708582759/5000000000000 : ℚ) : ℝ) ≤ stT385o2 135 := by
  have hc : ((64389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27708582759/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((64389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c136 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-977059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log ((136 : ℕ)) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((136 : ℕ)) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3658727/5000000) (δ := 4839/500000000) (ψ := 281281/1000000) 385 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t136 : ((-837864127737/10000000000000 : ℚ) : ℝ) ≤ stT385o2 136 := by
  have hc : ((-977109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-837864127737/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-977109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c137 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-366397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log ((137 : ℕ)) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((137 : ℕ)) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -608103/1250000) (δ := 9717/1000000000) (ψ := 281281/1000000) 385 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t137 : ((-156538463013/5000000000000 : ℚ) : ℝ) ≤ stT385o2 137 := by
  have hc : ((-366447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156538463013/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-366447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c138 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((427321/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log ((138 : ℕ)) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((138 : ℕ)) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1364837/10000000) (δ := 9667/1000000000) (ψ := 281281/1000000) 385 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t138 : ((1420852671/19531250000 : ℚ) : ℝ) ≤ stT385o2 138 := by
  have hc : ((13353/15625 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1420852671/19531250000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((13353/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c139 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((664499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log ((139 : ℕ)) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((139 : ℕ)) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 527483/2500000) (δ := 9817/1000000000) (ψ := 281281/1000000) 385 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t139 : ((140894417103/2500000000000 : ℚ) : ℝ) ≤ stT385o2 139 := by
  have hc : ((664449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140894417103/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((664449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c140 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-303831/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log ((140 : ℕ)) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((140 : ℕ)) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5559773/10000000) (δ := 9667/1000000000) (ψ := 281281/1000000) 385 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t140 : ((-3210067721/62500000000 : ℚ) : ℝ) ≤ stT385o2 140 := by
  have hc : ((-18991/31250 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3210067721/62500000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-18991/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c141 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-899393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log ((141 : ℕ)) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((141 : ℕ)) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6722941/10000000) (δ := 9793/1000000000) (ψ := 281281/1000000) 385 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t141 : ((-94683465167/1250000000000 : ℚ) : ℝ) ≤ stT385o2 141 := by
  have hc : ((-899443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94683465167/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-899443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c142 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((239699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log ((142 : ℕ)) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((142 : ℕ)) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3321851/10000000) (δ := 9793/1000000000) (ψ := 281281/1000000) 385 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t142 : ((201108887469/10000000000000 : ℚ) : ℝ) ≤ stT385o2 142 := by
  have hc : ((239649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201108887469/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((239649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c143 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((199951/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log ((143 : ℕ)) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((143 : ℕ)) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 55369/10000000) (δ := 9793/1000000000) (ψ := 281281/1000000) 385 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t143 : ((83599530861/1000000000000 : ℚ) : ℝ) ≤ stT385o2 143 := by
  have hc : ((199941/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83599530861/1000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((199941/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c144 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((102857/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log ((144 : ℕ)) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((144 : ℕ)) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3409007/10000000) (δ := 61/6250000) (ψ := 281281/1000000) 385 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t144 : ((5355831191/312500000000 : ℚ) : ℝ) ≤ stT385o2 144 := by
  have hc : ((6427/31250 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5355831191/312500000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((6427/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c145 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-902269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log ((145 : ℕ)) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((145 : ℕ)) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3369749/5000000) (δ := 9643/1000000000) (ψ := 281281/1000000) 385 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t145 : ((-149867065029/2000000000000 : ℚ) : ℝ) ≤ stT385o2 145 := by
  have hc : ((-902319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149867065029/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-902319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c146 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-159819/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log ((146 : ℕ)) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((146 : ℕ)) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2830441/5000000) (δ := 97/10000000) (ψ := 281281/1000000) 385 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t146 : ((-132277508389/2500000000000 : ℚ) : ℝ) ≤ stT385o2 146 := by
  have hc : ((-319663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132277508389/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-319663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c147 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((72673/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log ((147 : ℕ)) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((147 : ℕ)) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1187959/5000000) (δ := 9703/1000000000) (ψ := 281281/1000000) 385 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t147 : ((119869036131/2500000000000 : ℚ) : ℝ) ≤ stT385o2 147 := by
  have hc : ((290667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119869036131/2500000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((290667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c148 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((468871/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log ((148 : ℕ)) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((148 : ℕ)) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 886813/10000000) (δ := 97/10000000) (ψ := 281281/1000000) 385 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t148 : ((96347149731/1250000000000 : ℚ) : ℝ) ≤ stT385o2 148 := by
  have hc : ((234423/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96347149731/1250000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((234423/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c149 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-80157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log ((149 : ℕ)) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((149 : ℕ)) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2063799/5000000) (δ := 9803/1000000000) (ψ := 281281/1000000) 385 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t149 : ((-2053379407/312500000000 : ℚ) : ℝ) ≤ stT385o2 149 := by
  have hc : ((-80207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2053379407/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-80207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c150 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-489739/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log ((150 : ℕ)) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((150 : ℕ)) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 918329/1250000) (δ := 49/5000000) (ψ := 281281/1000000) 385 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t150 : ((-99972709177/1250000000000 : ℚ) : ℝ) ≤ stT385o2 150 := by
  have hc : ((-122441/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99972709177/1250000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-122441/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c151 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-118681/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log ((151 : ℕ)) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((151 : ℕ)) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2581809/5000000) (δ := 4823/500000000) (ψ := 281281/1000000) 385 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t151 : ((-193182929343/5000000000000 : ℚ) : ℝ) ≤ stT385o2 151 := by
  have hc : ((-237387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193182929343/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-237387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c152 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((700419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log ((152 : ℕ)) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((152 : ℕ)) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1987031/10000000) (δ := 9657/1000000000) (ψ := 281281/1000000) 385 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t152 : ((568074198483/10000000000000 : ℚ) : ℝ) ≤ stT385o2 152 := by
  have hc : ((700369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((568074198483/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((700369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c153 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((892703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log ((153 : ℕ)) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((153 : ℕ)) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 584359/5000000) (δ := 9757/1000000000) (ψ := 281281/1000000) 385 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t153 : ((180416775789/2500000000000 : ℚ) : ℝ) ≤ stT385o2 153 := by
  have hc : ((892653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180416775789/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((892653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c154 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-751/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log ((154 : ℕ)) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((154 : ℕ)) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4303917/10000000) (δ := 4823/500000000) (ψ := 281281/1000000) 385 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t154 : ((-484299623/40000000000 : ℚ) : ℝ) ≤ stT385o2 154 := by
  have hc : ((-601/4000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-484299623/40000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-601/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c155 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-123111/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log ((155 : ℕ)) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((155 : ℕ)) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 927351/1250000) (δ := 9757/1000000000) (ψ := 281281/1000000) 385 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t155 : ((-19778047509/250000000000 : ℚ) : ℝ) ≤ stT385o2 155 := by
  have hc : ((-492469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19778047509/250000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-492469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c156 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-97097/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log ((156 : ℕ)) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((156 : ℕ)) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1038857/2000000) (δ := 9639/1000000000) (ψ := 281281/1000000) 385 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t156 : ((-77747845587/2000000000000 : ℚ) : ℝ) ≤ stT385o2 156 := by
  have hc : ((-97107/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77747845587/2000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-97107/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c157 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((330863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log ((157 : ℕ)) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((157 : ℕ)) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1059597/5000000) (δ := 9739/1000000000) (ψ := 281281/1000000) 385 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t157 : ((66009294017/1250000000000 : ℚ) : ℝ) ≤ stT385o2 157 := by
  have hc : ((165419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66009294017/1250000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((165419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c158 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((37227/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log ((158 : ℕ)) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((158 : ℕ)) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 936359/10000000) (δ := 4857/500000000) (ψ := 281281/1000000) 385 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t158 : ((1184584373/16000000000 : ℚ) : ℝ) ≤ stT385o2 158 := by
  have hc : ((1489/1600 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1184584373/16000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((1489/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c159 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-18267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log ((159 : ℕ)) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((159 : ℕ)) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3972661/10000000) (δ := 9739/1000000000) (ψ := 281281/1000000) 385 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t159 : ((-3631583371/2500000000000 : ℚ) : ℝ) ≤ stT385o2 159 := by
  have hc : ((-18317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3631583371/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-18317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c160 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-470431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log ((160 : ℕ)) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((160 : ℕ)) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3494953/5000000) (δ := 9739/1000000000) (ψ := 281281/1000000) 385 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t160 : ((-4649104999/62500000000 : ℚ) : ℝ) ≤ stT385o2 160 := by
  have hc : ((-58807/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4649104999/62500000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-58807/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c161 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-41073/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log ((161 : ℕ)) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((161 : ℕ)) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5719629/10000000) (δ := 9681/1000000000) (ψ := 281281/1000000) 385 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t161 : ((-258980367599/5000000000000 : ℚ) : ℝ) ≤ stT385o2 161 := by
  have hc : ((-328609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258980367599/5000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-328609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c162 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((228627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log ((162 : ℕ)) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((162 : ℕ)) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2739729/10000000) (δ := 9681/1000000000) (ψ := 281281/1000000) 385 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t162 : ((44901661937/1250000000000 : ℚ) : ℝ) ≤ stT385o2 162 := by
  have hc : ((114301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44901661937/1250000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((114301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c163 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((498033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log ((163 : ℕ)) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((163 : ℕ)) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 55459/2500000) (δ := 4911/500000000) (ψ := 281281/1000000) 385 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t163 : ((2437935913/31250000000 : ℚ) : ℝ) ≤ stT385o2 163 := by
  have hc : ((62251/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2437935913/31250000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((62251/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c164 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((300001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log ((164 : ℕ)) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((164 : ℕ)) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3165257/10000000) (δ := 4861/500000000) (ψ := 281281/1000000) 385 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t164 : ((58555534367/2500000000000 : ℚ) : ℝ) ≤ stT385o2 164 := by
  have hc : ((299951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58555534367/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((299951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c165 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-761429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log ((165 : ℕ)) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((165 : ℕ)) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 761347/1250000) (δ := 4911/500000000) (ψ := 281281/1000000) 385 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t165 : ((-592810640021/10000000000000 : ℚ) : ℝ) ≤ stT385o2 165 := by
  have hc : ((-761479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-592810640021/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-761479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c166 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-897/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log ((166 : ℕ)) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((166 : ℕ)) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6709331/10000000) (δ := 4837/500000000) (ψ := 281281/1000000) 385 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t166 : ((-13924925091/200000000000 : ℚ) : ℝ) ≤ stT385o2 166 := by
  have hc : ((-17941/20000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13924925091/200000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-17941/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c167 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((1729/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log ((167 : ℕ)) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((167 : ℕ)) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -763779/2000000) (δ := 9729/1000000000) (ψ := 281281/1000000) 385 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t167 : ((1336392321/400000000000 : ℚ) : ℝ) ≤ stT385o2 167 := by
  have hc : ((1727/40000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1336392321/400000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((1727/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c168 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((929289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log ((168 : ℕ)) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((168 : ℕ)) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -189157/2000000) (δ := 4887/500000000) (ψ := 281281/1000000) 385 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t168 : ((179230689081/2500000000000 : ℚ) : ℝ) ≤ stT385o2 168 := by
  have hc : ((929239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179230689081/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((929239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c169 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((721981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log ((169 : ℕ)) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((169 : ℕ)) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 955169/5000000) (δ := 9679/1000000000) (ψ := 281281/1000000) 385 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t169 : ((55533098313/1000000000000 : ℚ) : ℝ) ≤ stT385o2 169 := by
  have hc : ((721931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55533098313/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((721931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c170 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-161563/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log ((170 : ℕ)) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((170 : ℕ)) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 37106/78125) (δ := 307/31250000) (ψ := 281281/1000000) 385 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t170 : ((-6196617021/250000000000 : ℚ) : ℝ) ≤ stT385o2 170 := by
  have hc : ((-40397/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6196617021/250000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-40397/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c171 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-248413/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log ((171 : ℕ)) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((171 : ℕ)) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1893037/2500000) (δ := 9679/1000000000) (ψ := 281281/1000000) 385 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t171 : ((-4749398709/62500000000 : ℚ) : ℝ) ≤ stT385o2 171 := by
  have hc : ((-496851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4749398709/62500000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-496851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c172 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-266051/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log ((172 : ℕ)) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((172 : ℕ)) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1065939/2000000) (δ := 9717/1000000000) (ψ := 281281/1000000) 385 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t172 : ((-50720271867/1250000000000 : ℚ) : ℝ) ≤ stT385o2 172 := by
  have hc : ((-66519/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50720271867/1250000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-66519/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c173 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((21073/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log ((173 : ℕ)) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((173 : ℕ)) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7937/31250) (δ := 4893/500000000) (ψ := 281281/1000000) 385 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t173 : ((3203993047/80000000000 : ℚ) : ℝ) ≤ stT385o2 173 := by
  have hc : ((21071/40000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3203993047/80000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((21071/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c174 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((1593/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log ((174 : ℕ)) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((174 : ℕ)) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 11697/500000) (δ := 9717/1000000000) (ψ := 281281/1000000) 385 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t174 : ((15094868327/200000000000 : ℚ) : ℝ) ≤ stT385o2 174 := by
  have hc : ((39823/40000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15094868327/200000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((39823/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c175 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((182699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log ((175 : ℕ)) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((175 : ℕ)) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 18699/62500) (δ := 4893/500000000) (ψ := 281281/1000000) 385 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t175 : ((8630524467/312500000000 : ℚ) : ℝ) ≤ stT385o2 175 := by
  have hc : ((91337/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8630524467/312500000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((91337/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c176 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-66149/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log ((176 : ℕ)) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((176 : ℕ)) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2867001/5000000) (δ := 9667/1000000000) (ψ := 281281/1000000) 385 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t176 : ((-24932747983/500000000000 : ℚ) : ℝ) ≤ stT385o2 176 := by
  have hc : ((-33077/50000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24932747983/500000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-33077/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c177 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-970699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log ((177 : ℕ)) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((177 : ℕ)) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1449459/2000000) (δ := 483/50000000) (ψ := 281281/1000000) 385 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t177 : ((-729660573603/10000000000000 : ℚ) : ℝ) ≤ stT385o2 177 := by
  have hc : ((-970749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-729660573603/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-970749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c178 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-241213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log ((178 : ℕ)) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((178 : ℕ)) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4536029/10000000) (δ := 61/6250000) (ψ := 281281/1000000) 385 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t178 : ((-45208584729/2500000000000 : ℚ) : ℝ) ≤ stT385o2 178 := by
  have hc : ((-241263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45208584729/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-241263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c179 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((741181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log ((179 : ℕ)) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((179 : ℕ)) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -919961/5000000) (δ := 971/100000000) (ψ := 281281/1000000) 385 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t179 : ((110789449797/2000000000000 : ℚ) : ℝ) ≤ stT385o2 179 := by
  have hc : ((741131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110789449797/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((741131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c180 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((943933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log ((180 : ℕ)) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((180 : ℕ)) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 420561/5000000) (δ := 9643/1000000000) (ψ := 281281/1000000) 385 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t180 : ((140705582693/2000000000000 : ℚ) : ℝ) ≤ stT385o2 180 := by
  have hc : ((943883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140705582693/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((943883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c181 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((5221/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log ((181 : ℕ)) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((181 : ℕ)) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3507343/10000000) (δ := 971/100000000) (ψ := 281281/1000000) 385 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t181 : ((31036612617/2500000000000 : ℚ) : ℝ) ≤ stT385o2 181 := by
  have hc : ((83511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31036612617/2500000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((83511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c182 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-778793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log ((182 : ℕ)) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((182 : ℕ)) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3079419/5000000) (δ := 971/100000000) (ψ := 281281/1000000) 385 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t182 : ((-461853899/8000000000 : ℚ) : ℝ) ≤ stT385o2 182 := by
  have hc : ((-778843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-461853899/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-778843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c183 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-929867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log ((183 : ℕ)) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((183 : ℕ)) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1728029/2500000) (δ := 9753/1000000000) (ψ := 281281/1000000) 385 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t183 : ((-343707552287/5000000000000 : ℚ) : ℝ) ≤ stT385o2 183 := by
  have hc : ((-929917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-343707552287/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-929917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c184 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-72247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log ((184 : ℕ)) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((184 : ℕ)) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -536187/1250000) (δ := 9753/1000000000) (ψ := 281281/1000000) 385 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t184 : ((-332997757/31250000000 : ℚ) : ℝ) ≤ stT385o2 184 := by
  have hc : ((-4517/31250 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-332997757/31250000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-4517/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c185 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((782311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log ((185 : ℕ)) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((185 : ℕ)) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1681073/10000000) (δ := 9803/1000000000) (ψ := 281281/1000000) 385 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t185 : ((287564619427/5000000000000 : ℚ) : ℝ) ≤ stT385o2 185 := by
  have hc : ((782261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((287564619427/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((782261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c186 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((934017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log ((186 : ℕ)) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((186 : ℕ)) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3653/40000) (δ := 193/20000000) (ψ := 281281/1000000) 385 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t186 : ((136963458649/2000000000000 : ℚ) : ℝ) ≤ stT385o2 186 := by
  have hc : ((933967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136963458649/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((933967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c187 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((34489/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log ((187 : ℕ)) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((187 : ℕ)) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 218357/625000) (δ := 9803/1000000000) (ψ := 281281/1000000) 385 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t187 : ((3151690911/250000000000 : ℚ) : ℝ) ≤ stT385o2 187 := by
  have hc : ((34479/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3151690911/250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((34479/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c188 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-376743/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log ((188 : ℕ)) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((188 : ℕ)) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6060363/10000000) (δ := 9653/1000000000) (ψ := 281281/1000000) 385 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t188 : ((-171741451/3125000000 : ℚ) : ℝ) ≤ stT385o2 188 := by
  have hc : ((-11774/15625 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171741451/3125000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-11774/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c189 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-954211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log ((189 : ℕ)) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((189 : ℕ)) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7094521/10000000) (δ := 303/31250000) (ψ := 281281/1000000) 385 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t189 : ((-694122771573/10000000000000 : ℚ) : ℝ) ≤ stT385o2 189 := by
  have hc : ((-954261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-694122771573/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-954261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c190 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-62139/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log ((190 : ℕ)) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((190 : ℕ)) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -910993/2000000) (δ := 2449/250000000) (ψ := 281281/1000000) 385 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t190 : ((-90178967531/5000000000000 : ℚ) : ℝ) ≤ stT385o2 190 := by
  have hc : ((-124303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90178967531/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-124303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c191 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((172107/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log ((191 : ℕ)) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((191 : ℕ)) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2028691/10000000) (δ := 303/31250000) (ψ := 281281/1000000) 385 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t191 : ((124523105743/2500000000000 : ℚ) : ℝ) ≤ stT385o2 191 := by
  have hc : ((344189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124523105743/2500000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((344189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c192 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((981291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log ((192 : ℕ)) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((192 : ℕ)) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 484349/10000000) (δ := 9807/1000000000) (ψ := 281281/1000000) 385 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t192 : ((708148873567/10000000000000 : ℚ) : ℝ) ≤ stT385o2 192 := by
  have hc : ((981241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((708148873567/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((981241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c193 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((368187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log ((193 : ℕ)) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((193 : ℕ)) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1492173/5000000) (δ := 4823/500000000) (ψ := 281281/1000000) 385 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t193 : ((52998106931/2000000000000 : ℚ) : ℝ) ≤ stT385o2 193 := by
  have hc : ((368137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52998106931/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((368137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c194 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-579229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log ((194 : ℕ)) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((194 : ℕ)) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2735723/5000000) (δ := 4823/500000000) (ψ := 281281/1000000) 385 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t194 : ((-415898571561/10000000000000 : ℚ) : ℝ) ≤ stT385o2 194 := by
  have hc : ((-579279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-415898571561/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-579279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c195 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-499663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log ((195 : ℕ)) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((195 : ℕ)) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3881109/5000000) (δ := 1963/200000000) (ψ := 281281/1000000) 385 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t195 : ((-8945851803/125000000000 : ℚ) : ℝ) ≤ stT385o2 195 := by
  have hc : ((-62461/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8945851803/125000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-62461/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c196 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-104441/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log ((196 : ℕ)) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((196 : ℕ)) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5300577/10000000) (δ := 2447/250000000) (ψ := 281281/1000000) 385 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t196 : ((-37303943493/1000000000000 : ℚ) : ℝ) ≤ stT385o2 196 := by
  have hc : ((-104451/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37303943493/1000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-104451/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c197 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((417069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log ((197 : ℕ)) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((197 : ℕ)) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2851447/10000000) (δ := 1943/200000000) (ψ := 281281/1000000) 385 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t197 : ((29711352693/1000000000000 : ℚ) : ℝ) ≤ stT385o2 197 := by
  have hc : ((417019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29711352693/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((417019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c198 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((986271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log ((198 : ℕ)) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((198 : ℕ)) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -207367/5000000) (δ := 1933/200000000) (ψ := 281281/1000000) 385 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t198 : ((700876691849/10000000000000 : ℚ) : ℝ) ≤ stT385o2 198 := by
  have hc : ((986221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((700876691849/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((986221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c199 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((173479/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log ((199 : ℕ)) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((199 : ℕ)) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2009707/10000000) (δ := 1211/125000000) (ψ := 281281/1000000) 385 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t199 : ((245934211973/5000000000000 : ℚ) : ℝ) ≤ stT385o2 199 := by
  have hc : ((346933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245934211973/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((346933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c200 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-98351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log ((200 : ℕ)) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((200 : ℕ)) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4421973/10000000) (δ := 1943/200000000) (ψ := 281281/1000000) 385 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t200 : ((-8695294779/625000000000 : ℚ) : ℝ) ≤ stT385o2 200 := by
  have hc : ((-12297/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8695294779/625000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-12297/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c201 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-183209/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log ((201 : ℕ)) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((201 : ℕ)) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1364451/2000000) (δ := 4869/500000000) (ψ := 281281/1000000) 385 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t201 : ((-64616394387/1000000000000 : ℚ) : ℝ) ≤ stT385o2 201 := by
  have hc : ((-183219/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64616394387/1000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-183219/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c202 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-428177/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log ((202 : ℕ)) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((202 : ℕ)) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6497409/10000000) (δ := 9781/1000000000) (ψ := 281281/1000000) 385 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t202 : ((-75320517699/1250000000000 : ℚ) : ℝ) ≤ stT385o2 202 := by
  have hc : ((-214101/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75320517699/1250000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-214101/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c203 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-77467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log ((203 : ℕ)) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((203 : ℕ)) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1030213/2500000) (δ := 9731/1000000000) (ψ := 281281/1000000) 385 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t203 : ((-54406314171/10000000000000 : ℚ) : ℝ) ≤ stT385o2 203 := by
  have hc : ((-77517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54406314171/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-77517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c204 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((763297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log ((204 : ℕ)) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((204 : ℕ)) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1755989/10000000) (δ := 4861/500000000) (ψ := 281281/1000000) 385 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t204 : ((26718987729/500000000000 : ℚ) : ℝ) ≤ stT385o2 204 := by
  have hc : ((763247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26718987729/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((763247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c205 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((121449/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log ((205 : ℕ)) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((205 : ℕ)) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 597323/10000000) (δ := 9731/1000000000) (ψ := 281281/1000000) 385 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t205 : ((33927703953/500000000000 : ℚ) : ℝ) ≤ stT385o2 205 := by
  have hc : ((485771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33927703953/500000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((485771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c206 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((192461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log ((206 : ℕ)) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((206 : ℕ)) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1469591/5000000) (δ := 9631/1000000000) (ψ := 281281/1000000) 385 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t206 : ((33519127897/1250000000000 : ℚ) : ℝ) ≤ stT385o2 206 := by
  have hc : ((48109/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33519127897/1250000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((48109/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c207 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-511627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log ((207 : ℕ)) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((207 : ℕ)) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5269683/10000000) (δ := 9731/1000000000) (ψ := 281281/1000000) 385 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t207 : ((-355640587173/10000000000000 : ℚ) : ℝ) ≤ stT385o2 207 := by
  have hc : ((-511677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-355640587173/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-511677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c208 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-994387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log ((208 : ℕ)) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((208 : ℕ)) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7588971/10000000) (δ := 9781/1000000000) (ψ := 281281/1000000) 385 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t208 : ((-5386865229/78125000000 : ℚ) : ℝ) ≤ stT385o2 208 := by
  have hc : ((-994437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5386865229/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-994437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c209 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-684219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log ((209 : ℕ)) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((209 : ℕ)) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5810821/10000000) (δ := 4887/500000000) (ψ := 281281/1000000) 385 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t209 : ((-94663826267/2000000000000 : ℚ) : ℝ) ≤ stT385o2 209 := by
  have hc : ((-684269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94663826267/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-684269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c210 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((5143/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log ((210 : ℕ)) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((210 : ℕ)) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -351367/1000000) (δ := 9629/1000000000) (ψ := 281281/1000000) 385 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t210 : ((11353363419/1000000000000 : ℚ) : ℝ) ≤ stT385o2 210 := by
  have hc : ((82263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11353363419/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((82263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c211 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((55117/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log ((211 : ℕ)) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((211 : ℕ)) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -306861/2500000) (δ := 2431/250000000) (ψ := 281281/1000000) 385 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t211 : ((75883869477/1250000000000 : ℚ) : ℝ) ≤ stT385o2 211 := by
  have hc : ((440911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75883869477/1250000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((440911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c212 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((456711/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log ((212 : ℕ)) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((212 : ℕ)) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 523977/5000000) (δ := 4887/500000000) (ψ := 281281/1000000) 385 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t212 : ((78413214543/1250000000000 : ℚ) : ℝ) ≤ stT385o2 212 := by
  have hc : ((228343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78413214543/1250000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((228343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c213 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((243263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log ((213 : ℕ)) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((213 : ℕ)) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3312669/10000000) (δ := 9729/1000000000) (ψ := 281281/1000000) 385 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t213 : ((41661657261/2500000000000 : ℚ) : ℝ) ≤ stT385o2 213 := by
  have hc : ((243213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41661657261/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((243213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c214 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-60989/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log ((214 : ℕ)) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((214 : ℕ)) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1391699/2500000) (δ := 9779/1000000000) (ψ := 281281/1000000) 385 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t214 : ((-10423661121/250000000000 : ℚ) : ℝ) ≤ stT385o2 214 := by
  have hc : ((-30497/50000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10423661121/250000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-30497/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c215 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-124981/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log ((215 : ℕ)) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((215 : ℕ)) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7810383/10000000) (δ := 4837/500000000) (ψ := 281281/1000000) 385 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t215 : ((-68192543651/1000000000000 : ℚ) : ℝ) ≤ stT385o2 215 := by
  have hc : ((-499949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68192543651/1000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-499949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c216 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-320177/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log ((216 : ℕ)) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((216 : ℕ)) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1416097/2500000) (δ := 9767/1000000000) (ψ := 281281/1000000) 385 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t216 : ((-54467480907/1250000000000 : ℚ) : ℝ) ≤ stT385o2 216 := by
  have hc : ((-160101/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54467480907/1250000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-160101/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c217 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((96481/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log ((217 : ℕ)) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((217 : ℕ)) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1720771/5000000) (δ := 2409/250000000) (ψ := 281281/1000000) 385 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t217 : ((2046205527/156250000000 : ℚ) : ℝ) ≤ stT385o2 217 := by
  have hc : ((12057/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2046205527/156250000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((12057/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c218 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((440799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log ((218 : ℕ)) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((218 : ℕ)) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1228899/10000000) (δ := 9667/1000000000) (ψ := 281281/1000000) 385 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t218 : ((29852961859/500000000000 : ℚ) : ℝ) ≤ stT385o2 218 := by
  have hc : ((220387/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29852961859/500000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((220387/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c219 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((231279/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log ((219 : ℕ)) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((219 : ℕ)) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 486819/5000000) (δ := 2409/250000000) (ψ := 281281/1000000) 385 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t219 : ((312550661821/5000000000000 : ℚ) : ℝ) ≤ stT385o2 219 := by
  have hc : ((462533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312550661821/5000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((462533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c220 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((299673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log ((220 : ℕ)) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((220 : ℕ)) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3166117/10000000) (δ := 1217/125000000) (ψ := 281281/1000000) 385 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t220 : ((202005526977/10000000000000 : ℚ) : ℝ) ≤ stT385o2 220 := by
  have hc : ((299623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202005526977/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((299623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c221 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-538517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log ((221 : ℕ)) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((221 : ℕ)) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2674341/5000000) (δ := 1217/125000000) (ψ := 281281/1000000) 385 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t221 : ((-362279479591/10000000000000 : ℚ) : ℝ) ≤ stT385o2 221 := by
  have hc : ((-538567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-362279479591/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-538567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c222 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-991161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log ((222 : ℕ)) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((222 : ℕ)) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7521333/10000000) (δ := 2409/250000000) (ψ := 281281/1000000) 385 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t222 : ((-665258201127/10000000000000 : ℚ) : ℝ) ≤ stT385o2 222 := by
  have hc : ((-991211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-665258201127/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-991211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c223 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-185941/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log ((223 : ℕ)) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((223 : ℕ)) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -60237/100000) (δ := 9743/1000000000) (ψ := 281281/1000000) 385 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t223 : ((-4980950451/100000000000 : ℚ) : ℝ) ≤ stT385o2 223 := by
  have hc : ((-371907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4980950451/100000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-371907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c224 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((22617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log ((224 : ℕ)) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((224 : ℕ)) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3870443/10000000) (δ := 9793/1000000000) (ψ := 281281/1000000) 385 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t224 : ((15078208751/10000000000000 : ℚ) : ℝ) ≤ stT385o2 224 := by
  have hc : ((22567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15078208751/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((22567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c225 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((770797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log ((225 : ℕ)) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((225 : ℕ)) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1726763/10000000) (δ := 9793/1000000000) (ψ := 281281/1000000) 385 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t225 : ((256915409751/5000000000000 : ℚ) : ℝ) ≤ stT385o2 225 := by
  have hc : ((770747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((256915409751/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((770747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c226 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((493377/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log ((226 : ℕ)) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((226 : ℕ)) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 101841/2500000) (δ := 19343/1000000000) (ψ := 281281/1000000) 385 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t226 : ((4102160211/62500000000 : ℚ) : ℝ) ≤ stT385o2 226 := by
  have hc : ((61669/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4102160211/62500000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((61669/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c227 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((529451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log ((227 : ℕ)) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((227 : ℕ)) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2532107/10000000) (δ := 9793/1000000000) (ψ := 281281/1000000) 385 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t227 : ((351375619923/10000000000000 : ℚ) : ℝ) ≤ stT385o2 227 := by
  have hc : ((529401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((351375619923/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((529401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c228 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-142113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log ((228 : ℕ)) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((228 : ℕ)) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4647489/10000000) (δ := 483/50000000) (ψ := 281281/1000000) 385 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t228 : ((-47066653423/2500000000000 : ℚ) : ℝ) ≤ stT385o2 228 := by
  have hc : ((-71069/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47066653423/2500000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-71069/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c229 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-226173/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log ((229 : ℕ)) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((229 : ℕ)) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 211051/312500) (δ := 9793/1000000000) (ψ := 281281/1000000) 385 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t229 : ((-298935351849/5000000000000 : ℚ) : ℝ) ≤ stT385o2 229 := by
  have hc : ((-452371/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-298935351849/5000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-452371/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c230 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-92159/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log ((230 : ℕ)) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((230 : ℕ)) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6857381/10000000) (δ := 193/20000000) (ψ := 281281/1000000) 385 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t230 : ((-15192797621/250000000000 : ℚ) : ℝ) ≤ stT385o2 230 := by
  have hc : ((-23041/25000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15192797621/250000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-23041/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c231 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-330671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log ((231 : ℕ)) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((231 : ℕ)) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2384763/5000000) (δ := 193/20000000) (ψ := 281281/1000000) 385 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t231 : ((-6799954481/312500000000 : ℚ) : ℝ) ≤ stT385o2 231 := by
  have hc : ((-330721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6799954481/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-330721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c232 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((474599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log ((232 : ℕ)) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((232 : ℕ)) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2690719/10000000) (δ := 9803/1000000000) (ψ := 281281/1000000) 385 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t232 : ((77889151017/2500000000000 : ℚ) : ℝ) ≤ stT385o2 232 := by
  have hc : ((474549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77889151017/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((474549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c233 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((38773/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log ((233 : ℕ)) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((233 : ℕ)) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -310407/5000000) (δ := 97/10000000) (ψ := 281281/1000000) 385 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t233 : ((25399696291/400000000000 : ℚ) : ℝ) ≤ stT385o2 233 := by
  have hc : ((38771/40000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25399696291/400000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((38771/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c234 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((838597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log ((234 : ℕ)) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((234 : ℕ)) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 288047/2000000) (δ := 9703/1000000000) (ψ := 281281/1000000) 385 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t234 : ((13704373621/250000000000 : ℚ) : ℝ) ≤ stT385o2 234 := by
  have hc : ((838547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13704373621/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((838547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c235 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((172931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log ((235 : ℕ)) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((235 : ℕ)) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1746239/5000000) (δ := 39/4000000) (ψ := 281281/1000000) 385 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t235 : ((14096889621/1250000000000 : ℚ) : ℝ) ≤ stT385o2 235 := by
  have hc : ((172881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14096889621/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((172881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c236 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-120017/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log ((236 : ℕ)) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((236 : ℕ)) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 553601/1000000) (δ := 49/5000000) (ψ := 281281/1000000) 385 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t236 : ((-15626195103/400000000000 : ℚ) : ℝ) ≤ stT385o2 236 := by
  have hc : ((-120027/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15626195103/400000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-120027/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c237 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-198719/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log ((237 : ℕ)) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((237 : ℕ)) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7570879/10000000) (δ := 193/20000000) (ψ := 281281/1000000) 385 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t237 : ((-12908839653/200000000000 : ℚ) : ℝ) ≤ stT385o2 237 := by
  have hc : ((-198729/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12908839653/200000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-198729/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c238 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-766591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log ((238 : ℕ)) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((238 : ℕ)) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6110781/10000000) (δ := 2427/250000000) (ψ := 281281/1000000) 385 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t238 : ((-124234940691/2500000000000 : ℚ) : ℝ) ≤ stT385o2 238 := by
  have hc : ((-766641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124234940691/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-766641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c239 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-33167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log ((239 : ℕ)) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((239 : ℕ)) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1023237/2500000) (δ := 4829/500000000) (ψ := 281281/1000000) 385 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t239 : ((-2683768203/625000000000 : ℚ) : ℝ) ≤ stT385o2 239 := by
  have hc : ((-4149/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2683768203/625000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-4149/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c240 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((21011/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log ((240 : ℕ)) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((240 : ℕ)) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2083537/10000000) (δ := 1939/200000000) (ψ := 281281/1000000) 385 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t240 : ((216984462047/5000000000000 : ℚ) : ℝ) ≤ stT385o2 240 := by
  have hc : ((336151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216984462047/5000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((336151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c241 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((31233/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log ((241 : ℕ)) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((241 : ℕ)) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -82499/10000000) (δ := 4879/500000000) (ψ := 281281/1000000) 385 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t241 : ((80471671417/1250000000000 : ℚ) : ℝ) ≤ stT385o2 241 := by
  have hc : ((499703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80471671417/1250000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((499703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c242 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((361001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log ((242 : ℕ)) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((242 : ℕ)) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1910261/10000000) (δ := 4879/500000000) (ψ := 281281/1000000) 385 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t242 : ((1812844033/39062500000 : ℚ) : ℝ) ≤ stT385o2 242 := by
  have hc : ((22561/31250 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1812844033/39062500000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((22561/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c243 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((161/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log ((243 : ℕ)) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((243 : ℕ)) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3894791/10000000) (δ := 1949/200000000) (ψ := 281281/1000000) 385 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t243 : ((1646089/2000000000 : ℚ) : ℝ) ≤ stT385o2 243 := by
  have hc : ((1283/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1646089/2000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((1283/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c244 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-175407/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log ((244 : ℕ)) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((244 : ℕ)) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5871189/10000000) (δ := 2427/250000000) (ψ := 281281/1000000) 385 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t244 : ((-44920373043/1000000000000 : ℚ) : ℝ) ≤ stT385o2 244 := by
  have hc : ((-350839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44920373043/1000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-350839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c245 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-999983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log ((245 : ℕ)) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((245 : ℕ)) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7839477/10000000) (δ := 3869/200000000) (ψ := 281281/1000000) 385 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t245 : ((-638898082941/10000000000000 : ℚ) : ℝ) ≤ stT385o2 245 := by
  have hc : ((-1000033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-638898082941/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-1000033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c246 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-142419/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log ((246 : ℕ)) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((246 : ℕ)) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2954093/5000000) (δ := 1953/200000000) (ψ := 281281/1000000) 385 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t246 : ((-90809454533/2000000000000 : ℚ) : ℝ) ≤ stT385o2 246 := by
  have hc : ((-142429/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90809454533/2000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-142429/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c247 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-1443/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log ((247 : ℕ)) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((247 : ℕ)) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3955851/10000000) (δ := 1953/200000000) (ψ := 281281/1000000) 385 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t247 : ((-737708829/1000000000000 : ℚ) : ℝ) ≤ stT385o2 247 := by
  have hc : ((-5797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-737708829/1000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-5797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c248 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((346713/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log ((248 : ℕ)) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((248 : ℕ)) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2011409/10000000) (δ := 1211/125000000) (ψ := 281281/1000000) 385 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t248 : ((687959/15625000 : ℚ) : ℝ) ≤ stT385o2 248 := by
  have hc : ((10834/15625 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((687959/15625000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((10834/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c249 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((15618/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log ((249 : ℕ)) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((249 : ℕ)) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -74811/10000000) (δ := 4869/500000000) (ψ := 281281/1000000) 385 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t249 : ((79176050681/1250000000000 : ℚ) : ℝ) ≤ stT385o2 249 := by
  have hc : ((499751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79176050681/1250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((499751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c250 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((147473/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log ((250 : ℕ)) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((250 : ℕ)) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1854087/10000000) (δ := 2447/250000000) (ψ := 281281/1000000) 385 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t250 : ((18652742333/400000000000 : ℚ) : ℝ) ≤ stT385o2 250 := by
  have hc : ((147463/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18652742333/400000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((147463/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c251 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((251 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((7583/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55254529/20000000 : ℚ) : ℝ) ≤ Real.log ((251 : ℕ)) / 2 := by
    have h := (log_br_251).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((251 : ℕ)) / 2 ≤ ((5525453/2000000 : ℚ) : ℝ) := by
    have h := (log_br_251).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3775237/10000000) (δ := 2447/250000000) (ψ := 281281/1000000) 385 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t251 : ((9564798279/2500000000000 : ℚ) : ℝ) ≤ stT385o2 251 := by
  have hc : ((30307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((251 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9564798279/2500000000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((30307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c252 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((252 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-161951/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5529429/2000000 : ℚ) : ℝ) ≤ Real.log ((252 : ℕ)) / 2 := by
    have h := (log_br_252).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((252 : ℕ)) / 2 ≤ ((55294291/20000000 : ℚ) : ℝ) := by
    have h := (log_br_252).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 177773/312500) (δ := 1963/200000000) (ψ := 281281/1000000) 385 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t252 : ((-204054898307/5000000000000 : ℚ) : ℝ) ≤ stT385o2 252 := by
  have hc : ((-323927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((252 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204054898307/5000000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-323927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c253 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((253 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-497313/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27666947/10000000 : ℚ) : ℝ) ≤ Real.log ((253 : ℕ)) / 2 := by
    have h := (log_br_253).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((253 : ℕ)) / 2 ≤ ((11066779/4000000 : ℚ) : ℝ) := by
    have h := (log_br_253).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3797339/5000000) (δ := 4819/500000000) (ψ := 281281/1000000) 385 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t253 : ((-31267391391/500000000000 : ℚ) : ℝ) ≤ stT385o2 253 := by
  have hc : ((-248669/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((253 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31267391391/500000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-248669/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c254 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((254 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-15853/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27686671/10000000 : ℚ) : ℝ) ≤ Real.log ((254 : ℕ)) / 2 := by
    have h := (log_br_254).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((254 : ℕ)) / 2 ≤ ((55373343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_254).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -124297/200000) (δ := 4861/500000000) (ψ := 281281/1000000) 385 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t254 : ((-19429077/390625000 : ℚ) : ℝ) ≤ stT385o2 254 := by
  have hc : ((-7927/10000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((254 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19429077/390625000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-7927/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c255 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((255 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-19761/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11082527/4000000 : ℚ) : ℝ) ≤ Real.log ((255 : ℕ)) / 2 := by
    have h := (log_br_255).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((255 : ℕ)) / 2 ≤ ((13853159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_255).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -34591/80000) (δ := 9781/1000000000) (ψ := 281281/1000000) 385 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t255 : ((-1980599381/200000000000 : ℚ) : ℝ) ≤ stT385o2 255 := by
  have hc : ((-79069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((255 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1980599381/200000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-79069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c256 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((256 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((560237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27725887/10000000 : ℚ) : ℝ) ≤ Real.log ((256 : ℕ)) / 2 := by
    have h := (log_br_256).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((256 : ℕ)) / 2 ≤ ((2218071/800000 : ℚ) : ℝ) := by
    have h := (log_br_256).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -244031/1000000) (δ := 4861/500000000) (ψ := 281281/1000000) 385 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t256 : ((560187/16000000 : ℚ) : ℝ) ≤ stT385o2 256 := by
  have hc : ((560187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((256 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((560187/16000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((560187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c257 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((257 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((19493/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1387269/500000 : ℚ) : ℝ) ≤ Real.log ((257 : ℕ)) / 2 := by
    have h := (log_br_257).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((257 : ℕ)) / 2 ≤ ((55490761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_257).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -564109/10000000) (δ := 9631/1000000000) (ψ := 281281/1000000) 385 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t257 : ((1519844843/25000000000 : ℚ) : ℝ) ≤ stT385o2 257 := by
  have hc : ((4873/5000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((257 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1519844843/25000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((4873/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c258 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((258 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((866859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11105919/4000000 : ℚ) : ℝ) ≤ Real.log ((258 : ℕ)) / 2 := by
    have h := (log_br_258).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((258 : ℕ)) / 2 ≤ ((13882399/5000000 : ℚ) : ℝ) := by
    have h := (log_br_258).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 52193/400000) (δ := 9781/1000000000) (ψ := 281281/1000000) 385 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t258 : ((134912753187/2500000000000 : ℚ) : ℝ) ≤ stT385o2 258 := by
  have hc : ((866809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((258 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134912753187/2500000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((866809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c259 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((259 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((299511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1389207/500000 : ℚ) : ℝ) ≤ Real.log ((259 : ℕ)) / 2 := by
    have h := (log_br_259).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((259 : ℕ)) / 2 ≤ ((55568281/20000000 : ℚ) : ℝ) := by
    have h := (log_br_259).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3166541/10000000) (δ := 9631/1000000000) (ψ := 281281/1000000) 385 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t259 : ((186075782109/10000000000000 : ℚ) : ℝ) ≤ stT385o2 259 := by
  have hc : ((299461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((259 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186075782109/10000000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((299461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c260 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((260 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-423801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1737713/625000 : ℚ) : ℝ) ≤ Real.log ((260 : ℕ)) / 2 := by
    have h := (log_br_260).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((260 : ℕ)) / 2 ≤ ((55606817/20000000 : ℚ) : ℝ) := by
    have h := (log_br_260).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2510543/5000000) (δ := 9631/1000000000) (ψ := 281281/1000000) 385 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t260 : ((-131430685037/5000000000000 : ℚ) : ℝ) ≤ stT385o2 260 := by
  have hc : ((-423851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((260 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131430685037/5000000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-423851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c261 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((261 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-230827/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13911301/5000000 : ℚ) : ℝ) ≤ Real.log ((261 : ℕ)) / 2 := by
    have h := (log_br_261).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((261 : ℕ)) / 2 ≤ ((11129041/4000000 : ℚ) : ℝ) := by
    have h := (log_br_261).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6868509/10000000) (δ := 4911/500000000) (ψ := 281281/1000000) 385 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t261 : ((-57154475163/1000000000000 : ℚ) : ℝ) ≤ stT385o2 261 := by
  have hc : ((-461679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((261 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57154475163/1000000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-461679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c262 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((262 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-942103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13920861/5000000 : ℚ) : ℝ) ≤ Real.log ((262 : ℕ)) / 2 := by
    have h := (log_br_262).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((262 : ℕ)) / 2 ≤ ((55683447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_262).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6999107/10000000) (δ := 907/31250000) (ψ := 281281/1000000) 385 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t262 : ((-582064949859/10000000000000 : ℚ) : ℝ) ≤ stT385o2 262 := by
  have hc : ((-942153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((262 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-582064949859/10000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-942153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c263 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((263 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-475487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2786077/1000000 : ℚ) : ℝ) ≤ Real.log ((263 : ℕ)) / 2 := by
    have h := (log_br_263).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((263 : ℕ)) / 2 ≤ ((55721541/20000000 : ℚ) : ℝ) := by
    have h := (log_br_263).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1033157/2000000) (δ := 2431/250000000) (ψ := 281281/1000000) 385 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t263 : ((-293228953699/10000000000000 : ℚ) : ℝ) ≤ stT385o2 263 := by
  have hc : ((-475537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((263 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).2
  have h0 : (0:ℝ) ≤ ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-293228953699/10000000000000 : ℚ) : ℝ)
      = ((616627/10000000 : ℚ) : ℝ) * ((-475537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c264 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((264 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((232881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5575949/2000000 : ℚ) : ℝ) ≤ Real.log ((264 : ℕ)) / 2 := by
    have h := (log_br_264).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((264 : ℕ)) / 2 ≤ ((55759493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_264).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3339393/10000000) (δ := 7231/250000000) (ψ := 281281/1000000) 385 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t264 : ((143297468767/10000000000000 : ℚ) : ℝ) ≤ stT385o2 264 := by
  have hc : ((232831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((264 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143297468767/10000000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((232831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c265 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((265 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((102601/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27898649/10000000 : ℚ) : ℝ) ≤ Real.log ((265 : ℕ)) / 2 := by
    have h := (log_br_265).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((265 : ℕ)) / 2 ≤ ((55797299/20000000 : ℚ) : ℝ) := by
    have h := (log_br_265).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1519931/10000000) (δ := 9629/1000000000) (ψ := 281281/1000000) 385 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t265 : ((50418753561/1000000000000 : ℚ) : ℝ) ≤ stT385o2 265 := by
  have hc : ((410379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((265 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50418753561/1000000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((410379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c266 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((266 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((496577/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55834963/20000000 : ℚ) : ℝ) ≤ Real.log ((266 : ℕ)) / 2 := by
    have h := (log_br_266).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((266 : ℕ)) / 2 ≤ ((13958741/5000000 : ℚ) : ℝ) := by
    have h := (log_br_266).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 292697/10000000) (δ := 4837/500000000) (ψ := 281281/1000000) 385 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t266 : ((38056924591/625000000000 : ℚ) : ℝ) ≤ stT385o2 266 := by
  have hc : ((62069/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((266 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).1
  have hw2 : ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((613139/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38056924591/625000000000 : ℚ) : ℝ)
      = ((613139/10000000 : ℚ) : ℝ) * ((62069/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c267 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((267 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((83489/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27936243/10000000 : ℚ) : ℝ) ≤ Real.log ((267 : ℕ)) / 2 := by
    have h := (log_br_267).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((267 : ℕ)) / 2 ≤ ((55872487/20000000 : ℚ) : ℝ) := by
    have h := (log_br_267).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2098491/10000000) (δ := 307/31250000) (ψ := 281281/1000000) 385 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t267 : ((20436243269/500000000000 : ℚ) : ℝ) ≤ stT385o2 267 := by
  have hc : ((333931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((267 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).1
  have hw2 : ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61199/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20436243269/500000000000 : ℚ) : ℝ)
      = ((61199/1000000 : ℚ) : ℝ) * ((333931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c268 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((268 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((11777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55909869/20000000 : ℚ) : ℝ) ≤ Real.log ((268 : ℕ)) / 2 := by
    have h := (log_br_268).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((268 : ℕ)) / 2 ≤ ((5590987/2000000 : ℚ) : ℝ) := by
    have h := (log_br_268).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 974387/2500000) (δ := 4887/500000000) (ψ := 281281/1000000) 385 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t268 : ((7163402769/10000000000000 : ℚ) : ℝ) ≤ stT385o2 268 := by
  have hc : ((11727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((268 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).1
  have hw2 : ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7163402769/10000000000000 : ℚ) : ℝ)
      = ((610847/10000000 : ℚ) : ℝ) * ((11727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c269 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((269 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-648163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55947113/20000000 : ℚ) : ℝ) ≤ Real.log ((269 : ℕ)) / 2 := by
    have h := (log_br_269).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((269 : ℕ)) / 2 ≤ ((27973557/10000000 : ℚ) : ℝ) := by
    have h := (log_br_269).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1422479/2500000) (δ := 9679/1000000000) (ψ := 281281/1000000) 385 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t269 : ((-395222596443/10000000000000 : ℚ) : ℝ) ≤ stT385o2 269 := by
  have hc : ((-648213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((269 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).2
  have h0 : (0:ℝ) ≤ ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-395222596443/10000000000000 : ℚ) : ℝ)
      = ((609711/10000000 : ℚ) : ℝ) * ((-648213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c270 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((270 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-988571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55984219/20000000 : ℚ) : ℝ) ≤ Real.log ((270 : ℕ)) / 2 := by
    have h := (log_br_270).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((270 : ℕ)) / 2 ≤ ((2799211/1000000 : ℚ) : ℝ) := by
    have h := (log_br_270).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3737821/5000000) (δ := 4837/500000000) (ψ := 281281/1000000) 385 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t270 : ((-601655956801/10000000000000 : ℚ) : ℝ) ≤ stT385o2 270 := by
  have hc : ((-988621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((270 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).2
  have h0 : (0:ℝ) ≤ ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-601655956801/10000000000000 : ℚ) : ℝ)
      = ((608581/10000000 : ℚ) : ℝ) * ((-988621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c271 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((271 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-423543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14005297/5000000 : ℚ) : ℝ) ≤ Real.log ((271 : ℕ)) / 2 := by
    have h := (log_br_271).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((271 : ℕ)) / 2 ≤ ((56021189/20000000 : ℚ) : ℝ) := by
    have h := (log_br_271).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1613297/2500000) (δ := 2409/250000000) (ψ := 281281/1000000) 385 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t271 : ((-16081209161/312500000000 : ℚ) : ℝ) ≤ stT385o2 271 := by
  have hc : ((-26473/31250 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((271 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).2
  have h0 : (0:ℝ) ≤ ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16081209161/312500000000 : ℚ) : ℝ)
      = ((607457/10000000 : ℚ) : ℝ) * ((-26473/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c272 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((272 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-296917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2802901/1000000 : ℚ) : ℝ) ≤ Real.log ((272 : ℕ)) / 2 := by
    have h := (log_br_272).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((272 : ℕ)) / 2 ≤ ((56058021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_272).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -585081/1250000) (δ := 2409/250000000) (ψ := 281281/1000000) 385 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t272 : ((-9003148539/500000000000 : ℚ) : ℝ) ≤ stT385o2 272 := by
  have hc : ((-296967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((272 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9003148539/500000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-296967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c273 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((273 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((393977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56094717/20000000 : ℚ) : ℝ) ≤ Real.log ((273 : ℕ)) / 2 := by
    have h := (log_br_273).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((273 : ℕ)) / 2 ≤ ((28047359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_273).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -582921/2000000) (δ := 9667/1000000000) (ψ := 281281/1000000) 385 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t273 : ((238415256429/10000000000000 : ℚ) : ℝ) ≤ stT385o2 273 := by
  have hc : ((393927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((273 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).1
  have hw2 : ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((605227/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238415256429/10000000000000 : ℚ) : ℝ)
      = ((605227/10000000 : ℚ) : ℝ) * ((393927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c274 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((274 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((89517/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56131281/20000000 : ℚ) : ℝ) ≤ Real.log ((274 : ℕ)) / 2 := by
    have h := (log_br_274).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((274 : ℕ)) / 2 ≤ ((28065641/10000000 : ℚ) : ℝ) := by
    have h := (log_br_274).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -577481/5000000) (δ := 4893/500000000) (ψ := 281281/1000000) 385 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t274 : ((3379760529/62500000000 : ℚ) : ℝ) ≤ stT385o2 274 := by
  have hc : ((11189/12500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((274 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).1
  have hw2 : ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((302061/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3379760529/62500000000 : ℚ) : ℝ)
      = ((302061/5000000 : ℚ) : ℝ) * ((11189/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c275 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((275 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((97151/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5616771/2000000 : ℚ) : ℝ) ≤ Real.log ((275 : ℕ)) / 2 := by
    have h := (log_br_275).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((275 : ℕ)) / 2 ≤ ((56167711/20000000 : ℚ) : ℝ) := by
    have h := (log_br_275).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 598183/10000000) (δ := 9717/1000000000) (ψ := 281281/1000000) 385 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t275 : ((14645293803/250000000000 : ℚ) : ℝ) ≤ stT385o2 275 := by
  have hc : ((48573/50000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((275 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).1
  have hw2 : ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((301511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14645293803/250000000000 : ℚ) : ℝ)
      = ((301511/5000000 : ℚ) : ℝ) * ((48573/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c276 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((276 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((295697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7025501/2500000 : ℚ) : ℝ) ≤ Real.log ((276 : ℕ)) / 2 := by
    have h := (log_br_276).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((276 : ℕ)) / 2 ≤ ((56204009/20000000 : ℚ) : ℝ) := by
    have h := (log_br_276).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 36641/156250) (δ := 9817/1000000000) (ψ := 281281/1000000) 385 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t276 : ((22246693911/625000000000 : ℚ) : ℝ) ≤ stT385o2 276 := by
  have hc : ((36959/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((276 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22246693911/625000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((36959/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c277 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((277 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-31693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2249607/800000 : ℚ) : ℝ) ≤ Real.log ((277 : ℕ)) / 2 := by
    have h := (log_br_277).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((277 : ℕ)) / 2 ≤ ((3515011/1250000 : ℚ) : ℝ) := by
    have h := (log_br_277).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4085561/10000000) (δ := 9767/1000000000) (ψ := 281281/1000000) 385 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t277 : ((-4764376639/1250000000000 : ℚ) : ℝ) ≤ stT385o2 277 := by
  have hc : ((-15859/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((277 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).2
  have h0 : (0:ℝ) ≤ ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4764376639/1250000000000 : ℚ) : ℝ)
      = ((300421/5000000 : ℚ) : ℝ) * ((-15859/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c278 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((278 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-42927/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56276211/20000000 : ℚ) : ℝ) ≤ Real.log ((278 : ℕ)) / 2 := by
    have h := (log_br_278).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((278 : ℕ)) / 2 ≤ ((14069053/5000000 : ℚ) : ℝ) := by
    have h := (log_br_278).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2909897/5000000) (δ := 4843/500000000) (ψ := 281281/1000000) 385 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t278 : ((-205982517601/5000000000000 : ℚ) : ℝ) ≤ stT385o2 278 := by
  have hc : ((-343441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((278 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).2
  have h0 : (0:ℝ) ≤ ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205982517601/5000000000000 : ℚ) : ℝ)
      = ((599761/10000000 : ℚ) : ℝ) * ((-343441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c279 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((279 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-248127/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56312117/20000000 : ℚ) : ℝ) ≤ Real.log ((279 : ℕ)) / 2 := by
    have h := (log_br_279).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((279 : ℕ)) / 2 ≤ ((28156059/10000000 : ℚ) : ℝ) := by
    have h := (log_br_279).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 754777/1000000) (δ := 9667/1000000000) (ψ := 281281/1000000) 385 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t279 : ((-59422958623/1000000000000 : ℚ) : ℝ) ≤ stT385o2 279 := by
  have hc : ((-496279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((279 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59422958623/1000000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-496279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c280 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((280 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-843913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7043487/2500000 : ℚ) : ℝ) ≤ Real.log ((280 : ℕ)) / 2 := by
    have h := (log_br_280).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((280 : ℕ)) / 2 ≤ ((56347897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_280).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6438329/10000000) (δ := 9709/1000000000) (ψ := 281281/1000000) 385 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t280 : ((-100872989649/2000000000000 : ℚ) : ℝ) ≤ stT385o2 280 := by
  have hc : ((-843963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((280 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100872989649/2000000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-843963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c281 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((281 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-312927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28191773/10000000 : ℚ) : ℝ) ≤ Real.log ((281 : ℕ)) / 2 := by
    have h := (log_br_281).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((281 : ℕ)) / 2 ≤ ((56383547/20000000 : ℚ) : ℝ) := by
    have h := (log_br_281).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4722673/10000000) (δ := 9809/1000000000) (ψ := 281281/1000000) 385 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t281 : ((-3734128587/200000000000 : ℚ) : ℝ) ≤ stT385o2 281 := by
  have hc : ((-312977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((281 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3734128587/200000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-312977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c282 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((282 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((89369/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5641907/2000000 : ℚ) : ℝ) ≤ Real.log ((282 : ℕ)) / 2 := by
    have h := (log_br_282).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((282 : ℕ)) / 2 ≤ ((56419071/20000000 : ℚ) : ℝ) := by
    have h := (log_br_282).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -75327/250000) (δ := 2411/250000000) (ψ := 281281/1000000) 385 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t282 : ((106421983083/5000000000000 : ℚ) : ℝ) ≤ stT385o2 282 := by
  have hc : ((178713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((282 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106421983083/5000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((178713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c283 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((283 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((173183/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14113617/5000000 : ℚ) : ℝ) ≤ Real.log ((283 : ℕ)) / 2 := by
    have h := (log_br_283).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((283 : ℕ)) / 2 ≤ ((56454469/20000000 : ℚ) : ℝ) := by
    have h := (log_br_283).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1309551/10000000) (δ := 609/62500000) (ψ := 281281/1000000) 385 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t283 : ((51470305887/1000000000000 : ℚ) : ℝ) ≤ stT385o2 283 := by
  have hc : ((173173/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((283 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51470305887/1000000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((173173/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c284 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((284 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((49399/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28244871/10000000 : ℚ) : ℝ) ≤ Real.log ((284 : ℕ)) / 2 := by
    have h := (log_br_284).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((284 : ℕ)) / 2 ≤ ((56489743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_284).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 38801/1000000) (δ := 2411/250000000) (ψ := 281281/1000000) 385 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t284 : ((5862277827/100000000000 : ℚ) : ℝ) ≤ stT385o2 284 := by
  have hc : ((98793/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((284 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5862277827/100000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((98793/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c285 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((285 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((67353/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56524891/20000000 : ℚ) : ℝ) ≤ Real.log ((285 : ℕ)) / 2 := by
    have h := (log_br_285).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((285 : ℕ)) / 2 ≤ ((14131223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_285).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 519889/2500000) (δ := 4897/500000000) (ψ := 281281/1000000) 385 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t285 : ((2493340819/62500000000 : ℚ) : ℝ) ≤ stT385o2 285 := by
  have hc : ((16837/25000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((285 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2493340819/62500000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((16837/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c286 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((286 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((64659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28279959/10000000 : ℚ) : ℝ) ≤ Real.log ((286 : ℕ)) / 2 := by
    have h := (log_br_286).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((286 : ℕ)) / 2 ≤ ((56559919/20000000 : ℚ) : ℝ) := by
    have h := (log_br_286).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 376523/1000000) (δ := 2411/250000000) (ψ := 281281/1000000) 385 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t286 : ((2387754813/625000000000 : ℚ) : ℝ) ≤ stT385o2 286 := by
  have hc : ((64609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((286 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).1
  have hw2 : ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((36957/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2387754813/625000000000 : ℚ) : ℝ)
      = ((36957/625000 : ℚ) : ℝ) * ((64609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c287 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((287 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-71321/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28297411/10000000 : ℚ) : ℝ) ≤ Real.log ((287 : ℕ)) / 2 := by
    have h := (log_br_287).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((287 : ℕ)) / 2 ≤ ((56594823/20000000 : ℚ) : ℝ) := by
    have h := (log_br_287).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1088997/2000000) (δ := 2411/250000000) (ψ := 281281/1000000) 385 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t287 : ((-84206383569/2500000000000 : ℚ) : ℝ) ≤ stT385o2 287 := by
  have hc : ((-285309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((287 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84206383569/2500000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-285309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c288 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((288 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-957079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14157401/5000000 : ℚ) : ℝ) ≤ Real.log ((288 : ℕ)) / 2 := by
    have h := (log_br_288).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((288 : ℕ)) / 2 ≤ ((11325921/4000000 : ℚ) : ℝ) := by
    have h := (log_br_288).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7118869/10000000) (δ := 609/62500000) (ψ := 281281/1000000) 385 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t288 : ((-70499250753/1250000000000 : ℚ) : ℝ) ≤ stT385o2 288 := by
  have hc : ((-957129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((288 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).2
  have h0 : (0:ℝ) ≤ ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70499250753/1250000000000 : ℚ) : ℝ)
      = ((73657/1250000 : ℚ) : ℝ) * ((-957129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c289 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((289 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-465583/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28332133/10000000 : ℚ) : ℝ) ≤ Real.log ((289 : ℕ)) / 2 := by
    have h := (log_br_289).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((289 : ℕ)) / 2 ≤ ((56664267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_289).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3460493/5000000) (δ := 4851/500000000) (ψ := 281281/1000000) 385 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t289 : ((-8558980859/156250000000 : ℚ) : ℝ) ≤ stT385o2 289 := by
  have hc : ((-58201/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((289 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).2
  have h0 : (0:ℝ) ≤ ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8558980859/156250000000 : ℚ) : ℝ)
      = ((147059/2500000 : ℚ) : ℝ) * ((-58201/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c290 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((290 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-253907/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56698809/20000000 : ℚ) : ℝ) ≤ Real.log ((290 : ℕ)) / 2 := by
    have h := (log_br_290).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((290 : ℕ)) / 2 ≤ ((5669881/2000000 : ℚ) : ℝ) := by
    have h := (log_br_290).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1314651/2500000) (δ := 2413/250000000) (ψ := 281281/1000000) 385 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t290 : ((-37278550743/1250000000000 : ℚ) : ℝ) ≤ stT385o2 290 := by
  have hc : ((-63483/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((290 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37278550743/1250000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-63483/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c291 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((291 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((4051/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3545827/1250000 : ℚ) : ℝ) ≤ Real.log ((291 : ℕ)) / 2 := by
    have h := (log_br_291).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((291 : ℕ)) / 2 ≤ ((56733233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_291).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3601997/10000000) (δ := 9651/1000000000) (ψ := 281281/1000000) 385 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t291 : ((3798113211/500000000000 : ℚ) : ℝ) ≤ stT385o2 291 := by
  have hc : ((64791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((291 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3798113211/500000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((64791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c292 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((292 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((355313/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28383769/10000000 : ℚ) : ℝ) ≤ Real.log ((292 : ℕ)) / 2 := by
    have h := (log_br_292).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((292 : ℕ)) / 2 ≤ ((56767539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_292).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1951021/10000000) (δ := 4851/500000000) (ψ := 281281/1000000) 385 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t292 : ((5197907851/125000000000 : ℚ) : ℝ) ≤ stT385o2 292 := by
  have hc : ((44411/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((292 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5197907851/125000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((44411/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c293 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((293 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((248133/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28400863/10000000 : ℚ) : ℝ) ≤ Real.log ((293 : ℕ)) / 2 := by
    have h := (log_br_293).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((293 : ℕ)) / 2 ≤ ((56801727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_293).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -305723/10000000) (δ := 9751/1000000000) (ψ := 281281/1000000) 385 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t293 : ((144953484823/2500000000000 : ℚ) : ℝ) ≤ stT385o2 293 := by
  have hc : ((496241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((293 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144953484823/2500000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((496241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c294 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((294 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((860993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56835797/20000000 : ℚ) : ℝ) ≤ Real.log ((294 : ℕ)) / 2 := by
    have h := (log_br_294).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((294 : ℕ)) / 2 ≤ ((28417899/10000000 : ℚ) : ℝ) := by
    have h := (log_br_294).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 166743/1250000) (δ := 9801/1000000000) (ψ := 281281/1000000) 385 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t294 : ((502111427973/10000000000000 : ℚ) : ℝ) ≤ stT385o2 294 := by
  have hc : ((860943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((294 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).1
  have hw2 : ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((583211/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((502111427973/10000000000000 : ℚ) : ℝ)
      = ((583211/10000000 : ℚ) : ℝ) * ((860943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c295 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((295 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((37423/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56869753/20000000 : ℚ) : ℝ) ≤ Real.log ((295 : ℕ)) / 2 := by
    have h := (log_br_295).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((295 : ℕ)) / 2 ≤ ((28434877/10000000 : ℚ) : ℝ) := by
    have h := (log_br_295).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 742019/2500000) (δ := 2413/250000000) (ψ := 281281/1000000) 385 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t295 : ((5446395699/250000000000 : ℚ) : ℝ) ≤ stT385o2 295 := by
  have hc : ((18709/50000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((295 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5446395699/250000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((18709/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c296 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((296 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-264681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28451797/10000000 : ℚ) : ℝ) ≤ Real.log ((296 : ℕ)) / 2 := by
    have h := (log_br_296).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((296 : ℕ)) / 2 ≤ ((11380719/4000000 : ℚ) : ℝ) := by
    have h := (log_br_296).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2298337/5000000) (δ := 4851/500000000) (ψ := 281281/1000000) 385 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t296 : ((-153871981709/10000000000000 : ℚ) : ℝ) ≤ stT385o2 296 := by
  have hc : ((-264731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((296 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153871981709/10000000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-264731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c297 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((297 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-198463/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56937321/20000000 : ℚ) : ℝ) ≤ Real.log ((297 : ℕ)) / 2 := by
    have h := (log_br_297).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((297 : ℕ)) / 2 ≤ ((28468661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_297).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3109893/5000000) (δ := 2413/250000000) (ψ := 281281/1000000) 385 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t297 : ((-230334390309/5000000000000 : ℚ) : ℝ) ≤ stT385o2 297 := by
  have hc : ((-396951/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((297 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230334390309/5000000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-396951/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c298 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((298 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-499989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28485467/10000000 : ℚ) : ℝ) ≤ Real.log ((298 : ℕ)) / 2 := by
    have h := (log_br_298).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((298 : ℕ)) / 2 ≤ ((11394187/4000000 : ℚ) : ℝ) := by
    have h := (log_br_298).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1959353/2500000) (δ := 9751/1000000000) (ψ := 281281/1000000) 385 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t298 : ((-28965060999/500000000000 : ℚ) : ℝ) ≤ stT385o2 298 := by
  have hc : ((-250007/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((298 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28965060999/500000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-250007/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c299 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((299 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-80313/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11400887/4000000 : ℚ) : ℝ) ≤ Real.log ((299 : ℕ)) / 2 := by
    have h := (log_br_299).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((299 : ℕ)) / 2 ≤ ((14251109/5000000 : ℚ) : ℝ) := by
    have h := (log_br_299).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1564579/2500000) (δ := 1929/200000000) (ψ := 281281/1000000) 385 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t299 : ((-4644910417/100000000000 : ℚ) : ℝ) ≤ stT385o2 299 := by
  have hc : ((-40159/50000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((299 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4644910417/100000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-40159/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c300 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((300 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-285753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((222804/78125 : ℚ) : ℝ) ≤ Real.log ((300 : ℕ)) / 2 := by
    have h := (log_br_300).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((300 : ℕ)) / 2 ≤ ((2281513/800000 : ℚ) : ℝ) := by
    have h := (log_br_300).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -465147/1000000) (δ := 4879/500000000) (ψ := 281281/1000000) 385 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t300 : ((-165008647853/10000000000000 : ℚ) : ℝ) ≤ stT385o2 300 := by
  have hc : ((-285803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((300 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165008647853/10000000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-285803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c301 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((301 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((171829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28535551/10000000 : ℚ) : ℝ) ≤ Real.log ((301 : ℕ)) / 2 := by
    have h := (log_br_301).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((301 : ℕ)) / 2 ≤ ((57071103/20000000 : ℚ) : ℝ) := by
    have h := (log_br_301).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3049967/10000000) (δ := 1959/200000000) (ψ := 281281/1000000) 385 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t301 : ((2475652689/125000000000 : ℚ) : ℝ) ≤ stT385o2 301 := by
  have hc : ((42951/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((301 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2475652689/125000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((42951/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c302 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((302 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((417819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5710427/2000000 : ℚ) : ℝ) ≤ Real.log ((302 : ℕ)) / 2 := by
    have h := (log_br_302).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((302 : ℕ)) / 2 ≤ ((57104271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_302).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1453757/10000000) (δ := 1959/200000000) (ψ := 281281/1000000) 385 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t302 : ((24041329039/500000000000 : ℚ) : ℝ) ≤ stT385o2 302 := by
  have hc : ((208897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((302 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24041329039/500000000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((208897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c303 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((303 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((199699/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3571083/1250000 : ℚ) : ℝ) ≤ Real.log ((303 : ℕ)) / 2 := by
    have h := (log_br_303).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((303 : ℕ)) / 2 ≤ ((57137329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_303).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3429/250000) (δ := 4879/500000000) (ψ := 281281/1000000) 385 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t303 : ((28679533869/500000000000 : ℚ) : ℝ) ≤ stT385o2 303 := by
  have hc : ((199689/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((303 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28679533869/500000000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((199689/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c304 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((304 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((385899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57170277/20000000 : ℚ) : ℝ) ≤ Real.log ((304 : ℕ)) / 2 := by
    have h := (log_br_304).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((304 : ℕ)) / 2 ≤ ((28585139/10000000 : ℚ) : ℝ) := by
    have h := (log_br_304).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 172283/1000000) (δ := 1949/200000000) (ψ := 281281/1000000) 385 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t304 : ((110656894043/2500000000000 : ℚ) : ℝ) ≤ stT385o2 304 := by
  have hc : ((192937/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((304 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).1
  have hw2 : ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110656894043/2500000000000 : ℚ) : ℝ)
      = ((573539/10000000 : ℚ) : ℝ) * ((192937/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c305 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((305 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((123457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57203117/20000000 : ℚ) : ℝ) ≤ Real.log ((305 : ℕ)) / 2 := by
    have h := (log_br_305).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((305 : ℕ)) / 2 ≤ ((28601559/10000000 : ℚ) : ℝ) := by
    have h := (log_br_305).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 660651/2000000) (δ := 1949/200000000) (ψ := 281281/1000000) 385 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t305 : ((4417307271/312500000000 : ℚ) : ℝ) ≤ stT385o2 305 := by
  have hc : ((15429/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((305 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4417307271/312500000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((15429/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c306 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((306 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-37151/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57235851/20000000 : ℚ) : ℝ) ≤ Real.log ((306 : ℕ)) / 2 := by
    have h := (log_br_306).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((306 : ℕ)) / 2 ≤ ((14308963/5000000 : ℚ) : ℝ) := by
    have h := (log_br_306).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4878579/10000000) (δ := 1929/200000000) (ψ := 281281/1000000) 385 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t306 : ((-2655084159/125000000000 : ℚ) : ℝ) ≤ stT385o2 306 := by
  have hc : ((-9289/25000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((306 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2655084159/125000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-9289/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c307 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((307 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-211533/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57268477/20000000 : ℚ) : ℝ) ≤ Real.log ((307 : ℕ)) / 2 := by
    have h := (log_br_307).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((307 : ℕ)) / 2 ≤ ((28634239/10000000 : ℚ) : ℝ) := by
    have h := (log_br_307).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1289741/2000000) (δ := 1949/200000000) (ψ := 281281/1000000) 385 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t307 : ((-241471149521/5000000000000 : ℚ) : ℝ) ≤ stT385o2 307 := by
  have hc : ((-423091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((307 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).2
  have h0 : (0:ℝ) ≤ ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241471149521/5000000000000 : ℚ) : ℝ)
      = ((570731/10000000 : ℚ) : ℝ) * ((-423091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c308 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((308 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-997959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57300997/20000000 : ℚ) : ℝ) ≤ Real.log ((308 : ℕ)) / 2 := by
    have h := (log_br_308).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((308 : ℕ)) / 2 ≤ ((28650499/10000000 : ℚ) : ℝ) := by
    have h := (log_br_308).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7694233/10000000) (δ := 4819/500000000) (ψ := 281281/1000000) 385 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t308 : ((-568668522227/10000000000000 : ℚ) : ℝ) ≤ stT385o2 308 := by
  have hc : ((-998009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((308 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).2
  have h0 : (0:ℝ) ≤ ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-568668522227/10000000000000 : ℚ) : ℝ)
      = ((569803/10000000 : ℚ) : ℝ) * ((-998009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c309 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((309 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-193147/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14333353/5000000 : ℚ) : ℝ) ≤ Real.log ((309 : ℕ)) / 2 := by
    have h := (log_br_309).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((309 : ℕ)) / 2 ≤ ((57333413/20000000 : ℚ) : ℝ) := by
    have h := (log_br_309).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6134261/10000000) (δ := 1933/200000000) (ψ := 281281/1000000) 385 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t309 : ((-219769539039/5000000000000 : ℚ) : ℝ) ≤ stT385o2 309 := by
  have hc : ((-386319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((309 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219769539039/5000000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-386319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c310 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((310 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-257989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28682861/10000000 : ℚ) : ℝ) ≤ Real.log ((310 : ℕ)) / 2 := by
    have h := (log_br_310).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((310 : ℕ)) / 2 ≤ ((57365723/20000000 : ℚ) : ℝ) := by
    have h := (log_br_310).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2289671/5000000) (δ := 1953/200000000) (ψ := 281281/1000000) 385 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t310 : ((-73278173259/5000000000000 : ℚ) : ℝ) ≤ stT385o2 310 := by
  have hc : ((-258039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((310 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73278173259/5000000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-258039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c311 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((311 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((17569/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57397929/20000000 : ℚ) : ℝ) ≤ Real.log ((311 : ℕ)) / 2 := by
    have h := (log_br_311).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((311 : ℕ)) / 2 ≤ ((5739793/2000000 : ℚ) : ℝ) := by
    have h := (log_br_311).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -151469/500000) (δ := 1963/200000000) (ψ := 281281/1000000) 385 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t311 : ((19922062251/1000000000000 : ℚ) : ℝ) ≤ stT385o2 311 := by
  have hc : ((35133/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((311 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19922062251/1000000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((35133/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c312 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((312 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((828827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57430031/20000000 : ℚ) : ℝ) ≤ Real.log ((312 : ℕ)) / 2 := by
    have h := (log_br_312).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((312 : ℕ)) / 2 ≤ ((3589377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_312).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -185559/1250000) (δ := 4869/500000000) (ψ := 281281/1000000) 385 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t312 : ((234601076613/5000000000000 : ℚ) : ℝ) ≤ stT385o2 312 := by
  have hc : ((828777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((312 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).1
  have hw2 : ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((283069/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234601076613/5000000000000 : ℚ) : ℝ)
      = ((283069/5000000 : ℚ) : ℝ) * ((828777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c313 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((313 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((999753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57462031/20000000 : ℚ) : ℝ) ≤ Real.log ((313 : ℕ)) / 2 := by
    have h := (log_br_313).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((313 : ℕ)) / 2 ≤ ((3591377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_313).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6941/1250000) (δ := 4869/500000000) (ψ := 281281/1000000) 385 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t313 : ((565065125799/10000000000000 : ℚ) : ℝ) ≤ stT385o2 313 := by
  have hc : ((999703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((313 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).1
  have hw2 : ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((565233/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((565065125799/10000000000000 : ℚ) : ℝ)
      = ((565233/10000000 : ℚ) : ℝ) * ((999703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c314 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((314 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((804331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57493929/20000000 : ℚ) : ℝ) ≤ Real.log ((314 : ℕ)) / 2 := by
    have h := (log_br_314).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((314 : ℕ)) / 2 ≤ ((5749393/2000000 : ℚ) : ℝ) := by
    have h := (log_br_314).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 79531/500000) (δ := 1963/200000000) (ψ := 281281/1000000) 385 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t314 : ((113470376323/2500000000000 : ℚ) : ℝ) ≤ stT385o2 314 := by
  have hc : ((804281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((314 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113470376323/2500000000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((804281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c315 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((315 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((316897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28762863/10000000 : ℚ) : ℝ) ≤ Real.log ((315 : ℕ)) / 2 := by
    have h := (log_br_315).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((315 : ℕ)) / 2 ≤ ((57525727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_315).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 62417/200000) (δ := 1211/125000000) (ψ := 281281/1000000) 385 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t315 : ((44630751573/2500000000000 : ℚ) : ℝ) ≤ stT385o2 315 := by
  have hc : ((316847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((315 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44630751573/2500000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((316847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c316 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((316 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-14187/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28778711/10000000 : ℚ) : ℝ) ≤ Real.log ((316 : ℕ)) / 2 := by
    have h := (log_br_316).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((316 : ℕ)) / 2 ≤ ((57557423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_316).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 232311/500000) (δ := 1211/125000000) (ψ := 281281/1000000) 385 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t316 : ((-997777261/62500000000 : ℚ) : ℝ) ≤ stT385o2 316 := by
  have hc : ((-28379/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((316 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-997777261/62500000000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-28379/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c317 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((317 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-780769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57589017/20000000 : ℚ) : ℝ) ≤ Real.log ((317 : ℕ)) / 2 := by
    have h := (log_br_317).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((317 : ℕ)) / 2 ≤ ((28794509/10000000 : ℚ) : ℝ) := by
    have h := (log_br_317).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 616673/1000000) (δ := 1963/200000000) (ψ := 281281/1000000) 385 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t317 : ((-54818959533/1250000000000 : ℚ) : ℝ) ≤ stT385o2 317 := by
  have hc : ((-780819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((317 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54818959533/1250000000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-780819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c318 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((318 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-62353/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57620513/20000000 : ℚ) : ℝ) ≤ Real.log ((318 : ℕ)) / 2 := by
    have h := (log_br_318).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((318 : ℕ)) / 2 ≤ ((28810257/10000000 : ℚ) : ℝ) := by
    have h := (log_br_318).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 307299/400000) (δ := 1963/200000000) (ψ := 281281/1000000) 385 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t318 : ((-279741050277/5000000000000 : ℚ) : ℝ) ≤ stT385o2 318 := by
  have hc : ((-498849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((318 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279741050277/5000000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-498849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c319 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((319 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-53741/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57651911/20000000 : ℚ) : ℝ) ≤ Real.log ((319 : ℕ)) / 2 := by
    have h := (log_br_319).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((319 : ℕ)) / 2 ≤ ((7206489/2500000 : ℚ) : ℝ) := by
    have h := (log_br_319).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -325723/500000) (δ := 9631/1000000000) (ψ := 281281/1000000) 385 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t319 : ((-240727675029/5000000000000 : ℚ) : ℝ) ≤ stT385o2 319 := by
  have hc : ((-429953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((319 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240727675029/5000000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-429953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c320 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((320 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-419143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57683209/20000000 : ℚ) : ℝ) ≤ Real.log ((320 : ℕ)) / 2 := by
    have h := (log_br_320).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((320 : ℕ)) / 2 ≤ ((5768321/2000000 : ℚ) : ℝ) := by
    have h := (log_br_320).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1252061/2500000) (δ := 9731/1000000000) (ψ := 281281/1000000) 385 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t320 : ((-234336013281/10000000000000 : ℚ) : ℝ) ≤ stT385o2 320 := by
  have hc : ((-419193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((320 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234336013281/10000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-419193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c321 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((321 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((83673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57714411/20000000 : ℚ) : ℝ) ≤ Real.log ((321 : ℕ)) / 2 := by
    have h := (log_br_321).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((321 : ℕ)) / 2 ≤ ((14428603/5000000 : ℚ) : ℝ) := by
    have h := (log_br_321).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3506647/10000000) (δ := 4911/500000000) (ψ := 281281/1000000) 385 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t321 : ((145899103/15625000000 : ℚ) : ℝ) ≤ stT385o2 321 := by
  have hc : ((2614/15625 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((321 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145899103/15625000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((2614/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c322 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((322 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((693899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11549103/4000000 : ℚ) : ℝ) ≤ Real.log ((322 : ℕ)) / 2 := by
    have h := (log_br_322).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((322 : ℕ)) / 2 ≤ ((14436379/5000000 : ℚ) : ℝ) := by
    have h := (log_br_322).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2009767/10000000) (δ := 4911/500000000) (ψ := 281281/1000000) 385 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t322 : ((193333391511/5000000000000 : ℚ) : ℝ) ≤ stT385o2 322 := by
  have hc : ((693849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((322 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193333391511/5000000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((693849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c323 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((323 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((978651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57776523/20000000 : ℚ) : ℝ) ≤ Real.log ((323 : ℕ)) / 2 := by
    have h := (log_br_323).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((323 : ℕ)) / 2 ≤ ((14444131/5000000 : ℚ) : ℝ) := by
    have h := (log_br_323).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -517507/10000000) (δ := 4911/500000000) (ψ := 281281/1000000) 385 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t323 : ((272253648407/5000000000000 : ℚ) : ℝ) ≤ stT385o2 323 := by
  have hc : ((978601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((323 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272253648407/5000000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((978601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c324 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((324 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((925647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11561487/4000000 : ℚ) : ℝ) ≤ Real.log ((324 : ℕ)) / 2 := by
    have h := (log_br_324).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((324 : ℕ)) / 2 ≤ ((14451859/5000000 : ℚ) : ℝ) := by
    have h := (log_br_324).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 970133/10000000) (δ := 4911/500000000) (ψ := 281281/1000000) 385 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t324 : ((102844008267/2000000000000 : ℚ) : ℝ) ≤ stT385o2 324 := by
  have hc : ((925597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((324 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102844008267/2000000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((925597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c325 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((325 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((22239/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57838251/20000000 : ℚ) : ℝ) ≤ Real.log ((325 : ℕ)) / 2 := by
    have h := (log_br_325).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((325 : ℕ)) / 2 ≤ ((14459563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_325).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2453153/10000000) (δ := 4911/500000000) (ψ := 281281/1000000) 385 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t325 : ((123348639/4000000000 : ℚ) : ℝ) ≤ stT385o2 325 := by
  have hc : ((22237/40000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((325 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123348639/4000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((22237/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c326 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((326 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-1863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57868973/20000000 : ℚ) : ℝ) ≤ Real.log ((326 : ℕ)) / 2 := by
    have h := (log_br_326).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((326 : ℕ)) / 2 ≤ ((28934487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_326).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3931649/10000000) (δ := 4861/500000000) (ψ := 281281/1000000) 385 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t326 : ((-1059513137/10000000000000 : ℚ) : ℝ) ≤ stT385o2 326 := by
  have hc : ((-1913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((326 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1059513137/10000000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-1913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c327 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((327 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-557567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57899601/20000000 : ℚ) : ℝ) ≤ Real.log ((327 : ℕ)) / 2 := by
    have h := (log_br_327).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((327 : ℕ)) / 2 ≤ ((28949801/10000000 : ℚ) : ℝ) := by
    have h := (log_br_327).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5405621/10000000) (δ := 9731/1000000000) (ψ := 281281/1000000) 385 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t327 : ((-154181658117/5000000000000 : ℚ) : ℝ) ≤ stT385o2 327 := by
  have hc : ((-557617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((327 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154181658117/5000000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-557617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c328 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((328 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-5777/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7241267/2500000 : ℚ) : ℝ) ≤ Real.log ((328 : ℕ)) / 2 := by
    have h := (log_br_328).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((328 : ℕ)) / 2 ≤ ((57930137/20000000 : ℚ) : ℝ) := by
    have h := (log_br_328).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3437559/5000000) (δ := 9681/1000000000) (ψ := 281281/1000000) 385 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t328 : ((-25519914523/500000000000 : ℚ) : ℝ) ≤ stT385o2 328 := by
  have hc : ((-92437/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((328 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25519914523/500000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-92437/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c329 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((329 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-196231/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57960577/20000000 : ℚ) : ℝ) ≤ Real.log ((329 : ℕ)) / 2 := by
    have h := (log_br_329).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((329 : ℕ)) / 2 ≤ ((28980289/10000000 : ℚ) : ℝ) := by
    have h := (log_br_329).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -115123/156250) (δ := 9629/1000000000) (ψ := 281281/1000000) 385 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t329 : ((-54095597819/1000000000000 : ℚ) : ℝ) ≤ stT385o2 329 := by
  have hc : ((-196241/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((329 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54095597819/1000000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-196241/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c330 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((330 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-355927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28995463/10000000 : ℚ) : ℝ) ≤ Real.log ((330 : ℕ)) / 2 := by
    have h := (log_br_330).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((330 : ℕ)) / 2 ≤ ((57990927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_330).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2953663/5000000) (δ := 9779/1000000000) (ψ := 281281/1000000) 385 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t330 : ((-6123286527/156250000000 : ℚ) : ℝ) ≤ stT385o2 330 := by
  have hc : ((-22247/31250 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((330 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6123286527/156250000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-22247/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c331 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((331 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-104077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58021183/20000000 : ℚ) : ℝ) ≤ Real.log ((331 : ℕ)) / 2 := by
    have h := (log_br_331).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((331 : ℕ)) / 2 ≤ ((906581/312500 : ℚ) : ℝ) := by
    have h := (log_br_331).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -556401/1250000) (δ := 9729/1000000000) (ψ := 281281/1000000) 385 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t331 : ((-572196643/50000000000 : ℚ) : ℝ) ≤ stT385o2 331 := by
  have hc : ((-52051/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((331 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-572196643/50000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-52051/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c332 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((332 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((72511/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58051349/20000000 : ℚ) : ℝ) ≤ Real.log ((332 : ℕ)) / 2 := by
    have h := (log_br_332).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((332 : ℕ)) / 2 ≤ ((1161027/400000 : ℚ) : ℝ) := by
    have h := (log_br_332).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -299947/1000000) (δ := 307/31250000) (ψ := 281281/1000000) 385 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t332 : ((39790071321/2000000000000 : ℚ) : ℝ) ≤ stT385o2 332 := by
  have hc : ((72501/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((332 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39790071321/2000000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((72501/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c333 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((333 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((203347/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3630089/1250000 : ℚ) : ℝ) ≤ Real.log ((333 : ℕ)) / 2 := by
    have h := (log_br_333).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((333 : ℕ)) / 2 ≤ ((2323257/800000 : ℚ) : ℝ) := by
    have h := (log_br_333).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -155211/1000000) (δ := 9679/1000000000) (ψ := 281281/1000000) 385 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t333 : ((55713246331/1250000000000 : ℚ) : ℝ) ≤ stT385o2 333 := by
  have hc : ((406669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((333 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55713246331/1250000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((406669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c334 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((334 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((124881/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58111409/20000000 : ℚ) : ℝ) ≤ Real.log ((334 : ℕ)) / 2 := by
    have h := (log_br_334).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((334 : ℕ)) / 2 ≤ ((5811141/2000000 : ℚ) : ℝ) := by
    have h := (log_br_334).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -54541/5000000) (δ := 9629/1000000000) (ψ := 281281/1000000) 385 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t334 : ((10932534613/200000000000 : ℚ) : ℝ) ≤ stT385o2 334 := by
  have hc : ((499499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((334 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10932534613/200000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((499499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c335 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((335 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((861863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11628261/4000000 : ℚ) : ℝ) ≤ Real.log ((335 : ℕ)) / 2 := by
    have h := (log_br_335).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((335 : ℕ)) / 2 ≤ ((29070653/10000000 : ℚ) : ℝ) := by
    have h := (log_br_335).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1329663/10000000) (δ := 9629/1000000000) (ψ := 281281/1000000) 385 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t335 : ((235429213527/5000000000000 : ℚ) : ℝ) ≤ stT385o2 335 := by
  have hc : ((861813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((335 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235429213527/5000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((861813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c336 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((336 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((448571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58171111/20000000 : ℚ) : ℝ) ≤ Real.log ((336 : ℕ)) / 2 := by
    have h := (log_br_336).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((336 : ℕ)) / 2 ≤ ((7271389/2500000 : ℚ) : ℝ) := by
    have h := (log_br_336).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2764077/10000000) (δ := 9729/1000000000) (ψ := 281281/1000000) 385 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t336 : ((30585992553/1250000000000 : ℚ) : ℝ) ≤ stT385o2 336 := by
  have hc : ((448521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((336 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30585992553/1250000000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((448521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c337 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((337 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-53351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58200829/20000000 : ℚ) : ℝ) ≤ Real.log ((337 : ℕ)) / 2 := by
    have h := (log_br_337).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((337 : ℕ)) / 2 ≤ ((5820083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_337).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 838851/2000000) (δ := 307/31250000) (ψ := 281281/1000000) 385 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t337 : ((-45430899/7812500000 : ℚ) : ℝ) ≤ stT385o2 337 := by
  have hc : ((-1668/15625 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((337 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45430899/7812500000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-1668/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c338 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((338 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-626663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29115229/10000000 : ℚ) : ℝ) ≤ Real.log ((338 : ℕ)) / 2 := by
    have h := (log_br_338).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((338 : ℕ)) / 2 ≤ ((58230459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_338).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5620151/10000000) (δ := 4837/500000000) (ψ := 281281/1000000) 385 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t338 : ((-340887375377/10000000000000 : ℚ) : ℝ) ≤ stT385o2 338 := by
  have hc : ((-626713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((338 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340887375377/10000000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-626713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c339 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((339 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-189541/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58260001/20000000 : ℚ) : ℝ) ≤ Real.log ((339 : ℕ)) / 2 := by
    have h := (log_br_339).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((339 : ℕ)) / 2 ≤ ((29130001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_339).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1760477/2500000) (δ := 9629/1000000000) (ψ := 281281/1000000) 385 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t339 : ((-51475038213/1000000000000 : ℚ) : ℝ) ≤ stT385o2 339 := by
  have hc : ((-189551/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((339 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51475038213/1000000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-189551/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c340 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((340 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-485409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3643091/1250000 : ℚ) : ℝ) ≤ Real.log ((340 : ℕ)) / 2 := by
    have h := (log_br_340).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((340 : ℕ)) / 2 ≤ ((58289457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_340).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7248533/10000000) (δ := 9787/1000000000) (ψ := 281281/1000000) 385 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t340 : ((-131631982459/2500000000000 : ℚ) : ℝ) ≤ stT385o2 340 := by
  have hc : ((-242717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((340 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131631982459/2500000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-242717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c341 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((341 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-691297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7289853/2500000 : ℚ) : ℝ) ≤ Real.log ((341 : ℕ)) / 2 := by
    have h := (log_br_341).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((341 : ℕ)) / 2 ≤ ((2332753/800000 : ℚ) : ℝ) := by
    have h := (log_br_341).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2917599/5000000) (δ := 9787/1000000000) (ψ := 281281/1000000) 385 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t341 : ((-374385832257/10000000000000 : ℚ) : ℝ) ≤ stT385o2 341 := by
  have hc : ((-691347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((341 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-374385832257/10000000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-691347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c342 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((342 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-198263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58348107/20000000 : ℚ) : ℝ) ≤ Real.log ((342 : ℕ)) / 2 := by
    have h := (log_br_342).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((342 : ℕ)) / 2 ≤ ((14587027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_342).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2212977/5000000) (δ := 9637/1000000000) (ψ := 281281/1000000) 385 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t342 : ((-107235573307/10000000000000 : ℚ) : ℝ) ≤ stT385o2 342 := by
  have hc : ((-198313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((342 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107235573307/10000000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-198313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c343 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((343 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((354573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7297163/2500000 : ℚ) : ℝ) ≤ Real.log ((343 : ℕ)) / 2 := by
    have h := (log_br_343).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((343 : ℕ)) / 2 ≤ ((11675461/4000000 : ℚ) : ℝ) := by
    have h := (log_br_343).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -188803/625000) (δ := 9787/1000000000) (ψ := 281281/1000000) 385 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t343 : ((191424339327/10000000000000 : ℚ) : ℝ) ≤ stT385o2 343 := by
  have hc : ((354523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((343 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191424339327/10000000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((354523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c344 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((344 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((797333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3650401/1250000 : ℚ) : ℝ) ≤ Real.log ((344 : ℕ)) / 2 := by
    have h := (log_br_344).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((344 : ℕ)) / 2 ≤ ((58406417/20000000 : ℚ) : ℝ) := by
    have h := (log_br_344).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1619833/10000000) (δ := 9787/1000000000) (ψ := 281281/1000000) 385 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t344 : ((429865494129/10000000000000 : ℚ) : ℝ) ≤ stT385o2 344 := by
  have hc : ((797283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((344 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((429865494129/10000000000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((797283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c345 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((345 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((996029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14608861/5000000 : ℚ) : ℝ) ≤ Real.log ((345 : ℕ)) / 2 := by
    have h := (log_br_345).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((345 : ℕ)) / 2 ≤ ((11687089/4000000 : ℚ) : ℝ) := by
    have h := (log_br_345).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -222861/10000000) (δ := 4833/500000000) (ψ := 281281/1000000) 385 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t345 : ((536216169999/10000000000000 : ℚ) : ℝ) ≤ stT385o2 345 := by
  have hc : ((995979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((345 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((536216169999/10000000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((995979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c346 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((346 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((223117/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58464387/20000000 : ℚ) : ℝ) ≤ Real.log ((346 : ℕ)) / 2 := by
    have h := (log_br_346).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((346 : ℕ)) / 2 ≤ ((14616097/5000000 : ℚ) : ℝ) := by
    have h := (log_br_346).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1170021/10000000) (δ := 9637/1000000000) (ψ := 281281/1000000) 385 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t346 : ((239883297027/5000000000000 : ℚ) : ℝ) ≤ stT385o2 346 := by
  have hc : ((446209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((346 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239883297027/5000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((446209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c347 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((347 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((260163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58493247/20000000 : ℚ) : ℝ) ≤ Real.log ((347 : ℕ)) / 2 := by
    have h := (log_br_347).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((347 : ℕ)) / 2 ≤ ((913957/312500 : ℚ) : ℝ) := by
    have h := (log_br_347).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 639727/2500000) (δ := 1227/125000000) (ψ := 281281/1000000) 385 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t347 : ((17456170283/625000000000 : ℚ) : ℝ) ≤ stT385o2 347 := by
  have hc : ((130069/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((347 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17456170283/625000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((130069/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c348 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((348 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-1681/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7315253/2500000 : ℚ) : ℝ) ≤ Real.log ((348 : ℕ)) / 2 := by
    have h := (log_br_348).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((348 : ℕ)) / 2 ≤ ((2340881/800000 : ℚ) : ℝ) := by
    have h := (log_br_348).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1971901/5000000) (δ := 9787/1000000000) (ψ := 281281/1000000) 385 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t348 : ((-1815625059/5000000000000 : ℚ) : ℝ) ≤ stT385o2 348 := by
  have hc : ((-3387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((348 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1815625059/5000000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-3387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c349 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((349 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-265213/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58550719/20000000 : ℚ) : ℝ) ≤ Real.log ((349 : ℕ)) / 2 := by
    have h := (log_br_349).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((349 : ℕ)) / 2 ≤ ((182971/62500 : ℚ) : ℝ) := by
    have h := (log_br_349).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1331187/2500000) (δ := 1227/125000000) (ψ := 281281/1000000) 385 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t349 : ((-8873669909/312500000000 : ℚ) : ℝ) ≤ stT385o2 349 := by
  have hc : ((-132619/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((349 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8873669909/312500000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-132619/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c350 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((350 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-895647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58579331/20000000 : ℚ) : ℝ) ≤ Real.log ((350 : ℕ)) / 2 := by
    have h := (log_br_350).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((350 : ℕ)) / 2 ≤ ((14644833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_350).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6701701/10000000) (δ := 9637/1000000000) (ψ := 281281/1000000) 385 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t350 : ((-478770647531/10000000000000 : ℚ) : ℝ) ≤ stT385o2 350 := by
  have hc : ((-895697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((350 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-478770647531/10000000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-895697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c351 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((351 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-996103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29303931/10000000 : ℚ) : ℝ) ≤ Real.log ((351 : ℕ)) / 2 := by
    have h := (log_br_351).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((351 : ℕ)) / 2 ≤ ((58607863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_351).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -954151/1250000) (δ := 9659/1000000000) (ψ := 281281/1000000) 385 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t351 : ((-531707621433/10000000000000 : ℚ) : ℝ) ≤ stT385o2 351 := by
  have hc : ((-996153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((351 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-531707621433/10000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-996153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c352 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((352 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-402253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58636311/20000000 : ℚ) : ℝ) ≤ Real.log ((352 : ℕ)) / 2 := by
    have h := (log_br_352).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((352 : ℕ)) / 2 ≤ ((7329539/2500000 : ℚ) : ℝ) := by
    have h := (log_br_352).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -62641/100000) (δ := 9709/1000000000) (ψ := 281281/1000000) 385 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t352 : ((-53603744639/1250000000000 : ℚ) : ℝ) ≤ stT385o2 352 := by
  have hc : ((-201139/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((352 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53603744639/1250000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-201139/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c353 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((353 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-379023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1466617/500000 : ℚ) : ℝ) ≤ Real.log ((353 : ℕ)) / 2 := by
    have h := (log_br_353).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((353 : ℕ)) / 2 ≤ ((58664681/20000000 : ℚ) : ℝ) := by
    have h := (log_br_353).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2449421/5000000) (δ := 9759/1000000000) (ψ := 281281/1000000) 385 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t353 : ((-201760467031/10000000000000 : ℚ) : ℝ) ≤ stT385o2 353 := by
  have hc : ((-379073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((353 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201760467031/10000000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-379073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c354 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((354 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((155193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58692969/20000000 : ℚ) : ℝ) ≤ Real.log ((354 : ℕ)) / 2 := by
    have h := (log_br_354).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((354 : ℕ)) / 2 ≤ ((5869297/2000000 : ℚ) : ℝ) := by
    have h := (log_br_354).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1768717/5000000) (δ := 9809/1000000000) (ψ := 281281/1000000) 385 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t354 : ((41228786821/5000000000000 : ℚ) : ℝ) ≤ stT385o2 354 := by
  have hc : ((155143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((354 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41228786821/5000000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((155143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c355 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((355 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((16083/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58721177/20000000 : ℚ) : ℝ) ≤ Real.log ((355 : ℕ)) / 2 := by
    have h := (log_br_355).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((355 : ℕ)) / 2 ≤ ((29360589/10000000 : ℚ) : ℝ) := by
    have h := (log_br_355).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -544981/2500000) (δ := 9809/1000000000) (ψ := 281281/1000000) 385 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t355 : ((4267646161/125000000000 : ℚ) : ℝ) ≤ stT385o2 355 := by
  have hc : ((64327/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((355 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4267646161/125000000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((64327/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c356 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((356 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((945891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58749307/20000000 : ℚ) : ℝ) ≤ Real.log ((356 : ℕ)) / 2 := by
    have h := (log_br_356).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((356 : ℕ)) / 2 ≤ ((14687327/5000000 : ℚ) : ℝ) := by
    have h := (log_br_356).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -826167/10000000) (δ := 609/62500000) (ψ := 281281/1000000) 385 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t356 : ((250646919159/5000000000000 : ℚ) : ℝ) ≤ stT385o2 356 := by
  have hc : ((945841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((356 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250646919159/5000000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((945841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c357 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((357 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((122267/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58777357/20000000 : ℚ) : ℝ) ≤ Real.log ((357 : ℕ)) / 2 := by
    have h := (log_br_357).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((357 : ℕ)) / 2 ≤ ((29388679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_357).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 523739/10000000) (δ := 2411/250000000) (ψ := 281281/1000000) 385 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t357 : ((32353617751/625000000000 : ℚ) : ℝ) ≤ stT385o2 357 := by
  have hc : ((489043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((357 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32353617751/625000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((489043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c358 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((358 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((18327/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58805329/20000000 : ℚ) : ℝ) ≤ Real.log ((358 : ℕ)) / 2 := by
    have h := (log_br_358).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((358 : ℕ)) / 2 ≤ ((5880533/2000000 : ℚ) : ℝ) := by
    have h := (log_br_358).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1869891/10000000) (δ := 9809/1000000000) (ψ := 281281/1000000) 385 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t358 : ((9685452087/250000000000 : ℚ) : ℝ) ≤ stT385o2 358 := by
  have hc : ((73303/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((358 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9685452087/250000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((73303/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c359 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((359 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((141001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58833223/20000000 : ℚ) : ℝ) ≤ Real.log ((359 : ℕ)) / 2 := by
    have h := (log_br_359).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((359 : ℕ)) / 2 ≤ ((7354153/2500000 : ℚ) : ℝ) := by
    have h := (log_br_359).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 321229/1000000) (δ := 9709/1000000000) (ψ := 281281/1000000) 385 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t359 : ((4650260769/312500000000 : ℚ) : ℝ) ≤ stT385o2 359 := by
  have hc : ((8811/31250 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((359 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4650260769/312500000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((8811/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c360 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((360 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-247013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((735763/250000 : ℚ) : ℝ) ≤ Real.log ((360 : ℕ)) / 2 := by
    have h := (log_br_360).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((360 : ℕ)) / 2 ≤ ((58861041/20000000 : ℚ) : ℝ) := by
    have h := (log_br_360).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4550983/10000000) (δ := 9759/1000000000) (ψ := 281281/1000000) 385 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t360 : ((-130213812961/10000000000000 : ℚ) : ℝ) ≤ stT385o2 360 := by
  have hc : ((-247063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((360 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130213812961/10000000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-247063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c361 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((361 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-141163/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58888779/20000000 : ℚ) : ℝ) ≤ Real.log ((361 : ℕ)) / 2 := by
    have h := (log_br_361).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((361 : ℕ)) / 2 ≤ ((2944439/1000000 : ℚ) : ℝ) := by
    have h := (log_br_361).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5885923/10000000) (δ := 609/62500000) (ψ := 281281/1000000) 385 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t361 : ((-18575402167/500000000000 : ℚ) : ℝ) ≤ stT385o2 361 := by
  have hc : ((-141173/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((361 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).2
  have h0 : (0:ℝ) ≤ ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18575402167/500000000000 : ℚ) : ℝ)
      = ((131579/2500000 : ℚ) : ℝ) * ((-141173/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c362 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((362 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-120967/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29458221/10000000 : ℚ) : ℝ) ≤ Real.log ((362 : ℕ)) / 2 := by
    have h := (log_br_362).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((362 : ℕ)) / 2 ≤ ((58916443/20000000 : ℚ) : ℝ) := by
    have h := (log_br_362).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1443441/2000000) (δ := 4897/500000000) (ψ := 281281/1000000) 385 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t362 : ((-254328837977/5000000000000 : ℚ) : ℝ) ≤ stT385o2 362 := by
  have hc : ((-483893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((362 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-254328837977/5000000000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-483893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c363 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((363 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-481033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14736007/5000000 : ℚ) : ℝ) ≤ Real.log ((363 : ℕ)) / 2 := by
    have h := (log_br_363).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((363 : ℕ)) / 2 ≤ ((58944029/20000000 : ℚ) : ℝ) := by
    have h := (log_br_363).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3581591/5000000) (δ := 9801/1000000000) (ψ := 281281/1000000) 385 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t363 : ((-1972578329/39062500000 : ℚ) : ℝ) ≤ stT385o2 363 := by
  have hc : ((-240529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((363 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1972578329/39062500000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-240529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c364 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((364 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-86559/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29485769/10000000 : ℚ) : ℝ) ≤ Real.log ((364 : ℕ)) / 2 := by
    have h := (log_br_364).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((364 : ℕ)) / 2 ≤ ((58971539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_364).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -182477/312500) (δ := 1219/125000000) (ψ := 281281/1000000) 385 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t364 : ((-181490279323/5000000000000 : ℚ) : ℝ) ≤ stT385o2 364 := by
  have hc : ((-346261/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((364 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181490279323/5000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-346261/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c365 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((365 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-234579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58998973/20000000 : ℚ) : ℝ) ≤ Real.log ((365 : ℕ)) / 2 := by
    have h := (log_br_365).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((365 : ℕ)) / 2 ≤ ((29499487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_365).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2259477/5000000) (δ := 9751/1000000000) (ψ := 281281/1000000) 385 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t365 : ((-3837826553/312500000000 : ℚ) : ℝ) ≤ stT385o2 365 := by
  have hc : ((-234629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((365 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3837826553/312500000000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-234629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c366 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((366 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((285851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59026333/20000000 : ℚ) : ℝ) ≤ Real.log ((366 : ℕ)) / 2 := by
    have h := (log_br_366).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((366 : ℕ)) / 2 ≤ ((29513167/10000000 : ℚ) : ℝ) := by
    have h := (log_br_366).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1601127/5000000) (δ := 9751/1000000000) (ψ := 281281/1000000) 385 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t366 : ((37347617277/2500000000000 : ℚ) : ℝ) ≤ stT385o2 366 := by
  have hc : ((285801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((366 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37347617277/2500000000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((285801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c367 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((367 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((145563/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29526809/10000000 : ℚ) : ℝ) ≤ Real.log ((367 : ℕ)) / 2 := by
    have h := (log_br_367).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((367 : ℕ)) / 2 ≤ ((59053619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_367).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -472291/2500000) (δ := 1219/125000000) (ψ := 281281/1000000) 385 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t367 : ((15195587647/400000000000 : ℚ) : ℝ) ≤ stT385o2 367 := by
  have hc : ((145553/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((367 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15195587647/400000000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((145553/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c368 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((368 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((486621/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59080829/20000000 : ℚ) : ℝ) ≤ Real.log ((368 : ℕ)) / 2 := by
    have h := (log_br_368).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((368 : ℕ)) / 2 ≤ ((5908083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_368).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -289817/5000000) (δ := 9751/1000000000) (ψ := 281281/1000000) 385 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t368 : ((31706960307/625000000000 : ℚ) : ℝ) ≤ stT385o2 368 := by
  have hc : ((121649/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((368 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31706960307/625000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((121649/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c369 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((369 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((958091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29553983/10000000 : ℚ) : ℝ) ≤ Real.log ((369 : ℕ)) / 2 := by
    have h := (log_br_369).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((369 : ℕ)) / 2 ≤ ((59107967/20000000 : ℚ) : ℝ) := by
    have h := (log_br_369).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 363167/5000000) (δ := 9701/1000000000) (ψ := 281281/1000000) 385 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t369 : ((498736025739/10000000000000 : ℚ) : ℝ) ≤ stT385o2 369 := by
  have hc : ((958041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((369 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((498736025739/10000000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((958041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c370 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((370 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((1721/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5913503/2000000 : ℚ) : ℝ) ≤ Real.log ((370 : ℕ)) / 2 := by
    have h := (log_br_370).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((370 : ℕ)) / 2 ≤ ((59135031/20000000 : ℚ) : ℝ) := by
    have h := (log_br_370).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2028789/10000000) (δ := 9701/1000000000) (ψ := 281281/1000000) 385 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t370 : ((57256953/1600000000 : ℚ) : ℝ) ≤ stT385o2 370 := by
  have hc : ((13767/20000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((370 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57256953/1600000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((13767/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c371 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((371 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((118717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2958101/1000000 : ℚ) : ℝ) ≤ Real.log ((371 : ℕ)) / 2 := by
    have h := (log_br_371).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((371 : ℕ)) / 2 ≤ ((59162021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_371).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3327683/10000000) (δ := 9801/1000000000) (ψ := 281281/1000000) 385 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t371 : ((7702725051/625000000000 : ℚ) : ℝ) ≤ stT385o2 371 := by
  have hc : ((29673/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((371 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).1
  have hw2 : ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((259587/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7702725051/625000000000 : ℚ) : ℝ)
      = ((259587/5000000 : ℚ) : ℝ) * ((29673/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c372 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((372 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-17179/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29594469/10000000 : ℚ) : ℝ) ≤ Real.log ((372 : ℕ)) / 2 := by
    have h := (log_br_372).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((372 : ℕ)) / 2 ≤ ((59188939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_372).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4623111/10000000) (δ := 1219/125000000) (ψ := 281281/1000000) 385 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t372 : ((-17817038883/1250000000000 : ℚ) : ℝ) ≤ stT385o2 372 := by
  have hc : ((-137457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((372 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17817038883/1250000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-137457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c373 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((373 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-714027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7401973/2500000 : ℚ) : ℝ) ≤ Real.log ((373 : ℕ)) / 2 := by
    have h := (log_br_373).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((373 : ℕ)) / 2 ≤ ((11843157/4000000 : ℚ) : ℝ) := by
    have h := (log_br_373).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 236603/400000) (δ := 2413/250000000) (ψ := 281281/1000000) 385 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t373 : ((-369735503137/10000000000000 : ℚ) : ℝ) ≤ stT385o2 373 := by
  have hc : ((-714077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((373 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369735503137/10000000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-714077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c374 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((374 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-966343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59242557/20000000 : ℚ) : ℝ) ≤ Real.log ((374 : ℕ)) / 2 := by
    have h := (log_br_374).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((374 : ℕ)) / 2 ≤ ((29621279/10000000 : ℚ) : ℝ) := by
    have h := (log_br_374).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3601763/5000000) (δ := 9751/1000000000) (ψ := 281281/1000000) 385 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t374 : ((-15615944487/312500000000 : ℚ) : ℝ) ≤ stT385o2 374 := by
  have hc : ((-966393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((374 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15615944487/312500000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-966393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c375 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((375 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-967953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2963463/1000000 : ℚ) : ℝ) ≤ Real.log ((375 : ℕ)) / 2 := by
    have h := (log_br_375).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((375 : ℕ)) / 2 ≤ ((59269261/20000000 : ℚ) : ℝ) := by
    have h := (log_br_375).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1804839/2500000) (δ := 1949/200000000) (ψ := 281281/1000000) 385 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t375 : ((-249937406597/5000000000000 : ℚ) : ℝ) ≤ stT385o2 375 := by
  have hc : ((-968003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((375 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249937406597/5000000000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-968003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c376 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((376 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-144069/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59295891/20000000 : ℚ) : ℝ) ≤ Real.log ((376 : ℕ)) / 2 := by
    have h := (log_br_376).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((376 : ℕ)) / 2 ≤ ((14823973/5000000 : ℚ) : ℝ) := by
    have h := (log_br_376).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5937739/10000000) (δ := 1939/200000000) (ψ := 281281/1000000) 385 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t376 : ((-74303125169/2000000000000 : ℚ) : ℝ) ≤ stT385o2 376 := by
  have hc : ((-144079/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((376 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74303125169/2000000000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-144079/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c377 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((377 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-72211/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59322451/20000000 : ℚ) : ℝ) ≤ Real.log ((377 : ℕ)) / 2 := by
    have h := (log_br_377).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((377 : ℕ)) / 2 ≤ ((14830613/5000000 : ℚ) : ℝ) := by
    have h := (log_br_377).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4659539/10000000) (δ := 1939/200000000) (ψ := 281281/1000000) 385 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t377 : ((-74394105069/5000000000000 : ℚ) : ℝ) ≤ stT385o2 377 := by
  have hc : ((-144447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((377 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).2
  have h0 : (0:ℝ) ≤ ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74394105069/5000000000000 : ℚ) : ℝ)
      = ((515027/10000000 : ℚ) : ℝ) * ((-144447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c378 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((378 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((13451/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59348941/20000000 : ℚ) : ℝ) ≤ Real.log ((378 : ℕ)) / 2 := by
    have h := (log_br_378).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((378 : ℕ)) / 2 ≤ ((29674471/10000000 : ℚ) : ℝ) := by
    have h := (log_br_378).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -846177/2500000) (δ := 1959/200000000) (ψ := 281281/1000000) 385 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t378 : ((6916833819/625000000000 : ℚ) : ℝ) ≤ stT385o2 378 := by
  have hc : ((107583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((378 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6916833819/625000000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((107583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c379 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((379 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((663523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29687681/10000000 : ℚ) : ℝ) ≤ Real.log ((379 : ℕ)) / 2 := by
    have h := (log_br_379).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((379 : ℕ)) / 2 ≤ ((59375363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_379).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2113197/10000000) (δ := 1929/200000000) (ψ := 281281/1000000) 385 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t379 : ((68160571709/2000000000000 : ℚ) : ℝ) ≤ stT385o2 379 := by
  have hc : ((663473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((379 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68160571709/2000000000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((663473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c380 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((380 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((471703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3712607/1250000 : ℚ) : ℝ) ≤ Real.log ((380 : ℕ)) / 2 := by
    have h := (log_br_380).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((380 : ℕ)) / 2 ≤ ((59401713/20000000 : ℚ) : ℝ) := by
    have h := (log_br_380).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -845103/10000000) (δ := 2427/250000000) (ψ := 281281/1000000) 385 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t380 : ((120982812771/2500000000000 : ℚ) : ℝ) ≤ stT385o2 380 := by
  have hc : ((235839/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((380 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120982812771/2500000000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((235839/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c381 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((381 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((985943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59427993/20000000 : ℚ) : ℝ) ≤ Real.log ((381 : ℕ)) / 2 := by
    have h := (log_br_381).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((381 : ℕ)) / 2 ≤ ((29713997/10000000 : ℚ) : ℝ) := by
    have h := (log_br_381).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 41967/1000000) (δ := 4829/500000000) (ψ := 281281/1000000) 385 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t381 : ((101017554459/2000000000000 : ℚ) : ℝ) ≤ stT385o2 381 := by
  have hc : ((985893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((381 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101017554459/2000000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((985893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c382 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((382 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((391143/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29727103/10000000 : ℚ) : ℝ) ≤ Real.log ((382 : ℕ)) / 2 := by
    have h := (log_br_382).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((382 : ℕ)) / 2 ≤ ((59454207/20000000 : ℚ) : ℝ) := by
    have h := (log_br_382).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1681171/10000000) (δ := 613/62500000) (ψ := 281281/1000000) 385 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t382 : ((25014147249/625000000000 : ℚ) : ℝ) ≤ stT385o2 382 := by
  have hc : ((195559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((382 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25014147249/625000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((195559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c383 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((383 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((192439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59480349/20000000 : ℚ) : ℝ) ≤ Real.log ((383 : ℕ)) / 2 := by
    have h := (log_br_383).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((383 : ℕ)) / 2 ≤ ((1189607/400000 : ℚ) : ℝ) := by
    have h := (log_br_383).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1469651/5000000) (δ := 1959/200000000) (ψ := 281281/1000000) 385 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t383 : ((48007293/2441406250 : ℚ) : ℝ) ≤ stT385o2 383 := by
  have hc : ((96207/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((383 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48007293/2441406250 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((96207/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c384 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((384 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-26671/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2380257/800000 : ℚ) : ℝ) ≤ Real.log ((384 : ℕ)) / 2 := by
    have h := (log_br_384).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((384 : ℕ)) / 2 ≤ ((29753213/10000000 : ℚ) : ℝ) := by
    have h := (log_br_384).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 419421/1000000) (δ := 4829/500000000) (ψ := 281281/1000000) 385 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t384 : ((-27233767137/5000000000000 : ℚ) : ℝ) ≤ stT385o2 384 := by
  have hc : ((-53367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((384 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27233767137/5000000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-53367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c385 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((385 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-570851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59532433/20000000 : ℚ) : ℝ) ≤ Real.log ((385 : ℕ)) / 2 := by
    have h := (log_br_385).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((385 : ℕ)) / 2 ≤ ((29766217/10000000 : ℚ) : ℝ) := by
    have h := (log_br_385).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1089169/2000000) (δ := 4829/500000000) (ψ := 281281/1000000) 385 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t385 : ((-18184909553/625000000000 : ℚ) : ℝ) ≤ stT385o2 385 := by
  have hc : ((-570901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((385 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18184909553/625000000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-570901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c386 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((386 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-89431/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59558373/20000000 : ℚ) : ℝ) ≤ Real.log ((386 : ℕ)) / 2 := by
    have h := (log_br_386).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((386 : ℕ)) / 2 ≤ ((29779187/10000000 : ℚ) : ℝ) := by
    have h := (log_br_386).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6694207/10000000) (δ := 1959/200000000) (ψ := 281281/1000000) 385 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t386 : ((-11380440333/250000000000 : ℚ) : ℝ) ≤ stT385o2 386 := by
  have hc : ((-22359/25000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((386 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11380440333/250000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-22359/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c387 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((387 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-999417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29792123/10000000 : ℚ) : ℝ) ≤ Real.log ((387 : ℕ)) / 2 := by
    have h := (log_br_387).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((387 : ℕ)) / 2 ≤ ((59584247/20000000 : ℚ) : ℝ) := by
    have h := (log_br_387).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3884309/5000000) (δ := 4869/500000000) (ψ := 281281/1000000) 385 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t387 : ((-508058060643/10000000000000 : ℚ) : ℝ) ≤ stT385o2 387 := by
  have hc : ((-999467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((387 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-508058060643/10000000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-999467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c388 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((388 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-13474/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59610053/20000000 : ℚ) : ℝ) ≤ Real.log ((388 : ℕ)) / 2 := by
    have h := (log_br_388).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((388 : ℕ)) / 2 ≤ ((29805027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_388).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -101979/156250) (δ := 1211/125000000) (ψ := 281281/1000000) 385 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t388 : ((-109452737541/2500000000000 : ℚ) : ℝ) ≤ stT385o2 388 := by
  have hc : ((-431193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((388 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109452737541/2500000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-431193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c389 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((389 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-12947/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59635793/20000000 : ℚ) : ℝ) ≤ Real.log ((389 : ℕ)) / 2 := by
    have h := (log_br_389).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((389 : ℕ)) / 2 ≤ ((29817897/10000000 : ℚ) : ℝ) := by
    have h := (log_br_389).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2643959/5000000) (δ := 1953/200000000) (ψ := 281281/1000000) 385 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t389 : ((-26260138653/1000000000000 : ℚ) : ℝ) ≤ stT385o2 389 := by
  have hc : ((-51793/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((389 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26260138653/1000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-51793/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c390 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((390 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-401/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59661467/20000000 : ℚ) : ℝ) ≤ Real.log ((390 : ℕ)) / 2 := by
    have h := (log_br_390).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((390 : ℕ)) / 2 ≤ ((14915367/5000000 : ℚ) : ℝ) := by
    have h := (log_br_390).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4052357/10000000) (δ := 1933/200000000) (ψ := 281281/1000000) 385 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t390 : ((-101628459/40000000000 : ℚ) : ℝ) ≤ stT385o2 390 := by
  have hc : ((-2007/40000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((390 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101628459/40000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-2007/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c391 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((391 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((214239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2387483/800000 : ℚ) : ℝ) ≤ Real.log ((391 : ℕ)) / 2 := by
    have h := (log_br_391).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((391 : ℕ)) / 2 ≤ ((14921769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_391).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -704993/2500000) (δ := 1933/200000000) (ψ := 281281/1000000) 385 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t391 : ((54166259147/2500000000000 : ℚ) : ℝ) ≤ stT385o2 391 := by
  have hc : ((107107/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((391 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54166259147/2500000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((107107/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c392 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((392 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((201077/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29856309/10000000 : ℚ) : ℝ) ≤ Real.log ((392 : ℕ)) / 2 := by
    have h := (log_br_392).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((392 : ℕ)) / 2 ≤ ((59712619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_392).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -318143/2000000) (δ := 1943/200000000) (ψ := 281281/1000000) 385 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t392 : ((50776426701/1250000000000 : ℚ) : ℝ) ≤ stT385o2 392 := by
  have hc : ((402129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((392 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50776426701/1250000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((402129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c393 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((393 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((197877/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3733631/1250000 : ℚ) : ℝ) ≤ Real.log ((393 : ℕ)) / 2 := by
    have h := (log_br_393).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((393 : ℕ)) / 2 ≤ ((59738097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_393).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -182293/5000000) (δ := 1963/200000000) (ψ := 281281/1000000) 385 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t393 : ((99810644411/2000000000000 : ℚ) : ℝ) ≤ stT385o2 393 := by
  have hc : ((197867/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((393 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99810644411/2000000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((197867/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c394 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((394 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((941627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59763509/20000000 : ℚ) : ℝ) ≤ Real.log ((394 : ℕ)) / 2 := by
    have h := (log_br_394).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((394 : ℕ)) / 2 ≤ ((5976351/2000000 : ℚ) : ℝ) := by
    have h := (log_br_394).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 429207/5000000) (δ := 1211/125000000) (ψ := 281281/1000000) 385 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t394 : ((29647434999/625000000000 : ℚ) : ℝ) ≤ stT385o2 394 := by
  have hc : ((941577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((394 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29647434999/625000000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((941577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c395 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((395 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((134781/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59788857/20000000 : ℚ) : ℝ) ≤ Real.log ((395 : ℕ)) / 2 := by
    have h := (log_br_395).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((395 : ℕ)) / 2 ≤ ((29894429/10000000 : ℚ) : ℝ) := by
    have h := (log_br_395).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2078287/10000000) (δ := 1953/200000000) (ψ := 281281/1000000) 385 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t395 : ((33905283867/1000000000000 : ℚ) : ℝ) ≤ stT385o2 395 := by
  have hc : ((134771/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((395 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33905283867/1000000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((134771/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c396 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((396 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((250063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29907071/10000000 : ℚ) : ℝ) ≤ Real.log ((396 : ℕ)) / 2 := by
    have h := (log_br_396).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((396 : ℕ)) / 2 ≤ ((59814143/20000000 : ℚ) : ℝ) := by
    have h := (log_br_396).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3295127/10000000) (δ := 4869/500000000) (ψ := 281281/1000000) 385 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t396 : ((62818016367/5000000000000 : ℚ) : ℝ) ≤ stT385o2 396 := by
  have hc : ((250013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((396 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62818016367/5000000000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((250013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c397 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((397 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-57661/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29919681/10000000 : ℚ) : ℝ) ≤ Real.log ((397 : ℕ)) / 2 := by
    have h := (log_br_397).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((397 : ℕ)) / 2 ≤ ((59839363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_397).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 112721/250000) (δ := 1943/200000000) (ψ := 281281/1000000) 385 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t397 : ((-28945522221/2500000000000 : ℚ) : ℝ) ≤ stT385o2 397 := by
  have hc : ((-115347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((397 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28945522221/2500000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-115347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c398 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((398 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-13143/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1496613/500000 : ℚ) : ℝ) ≤ Real.log ((398 : ℕ)) / 2 := by
    have h := (log_br_398).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((398 : ℕ)) / 2 ≤ ((59864521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_398).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5719569/10000000) (δ := 1963/200000000) (ψ := 281281/1000000) 385 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t398 : ((-164712393/5000000000 : ℚ) : ℝ) ≤ stT385o2 398 := by
  have hc : ((-1643/2500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((398 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164712393/5000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-1643/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c399 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((399 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-116509/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29944807/10000000 : ℚ) : ℝ) ≤ Real.log ((399 : ℕ)) / 2 := by
    have h := (log_br_399).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((399 : ℕ)) / 2 ≤ ((11977923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_399).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6927217/10000000) (δ := 4869/500000000) (ψ := 281281/1000000) 385 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t399 : ((-233322720247/5000000000000 : ℚ) : ℝ) ≤ stT385o2 399 := by
  have hc : ((-466061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((399 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233322720247/5000000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-466061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c400 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((400 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-99383/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11982929/4000000 : ℚ) : ℝ) ≤ Real.log ((400 : ℕ)) / 2 := by
    have h := (log_br_400).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((400 : ℕ)) / 2 ≤ ((29957323/10000000 : ℚ) : ℝ) := by
    have h := (log_br_400).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7576129/10000000) (δ := 9673/1000000000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t400 : ((-12423524847/250000000000 : ℚ) : ℝ) ≤ stT385o2 400 := by
  have hc : ((-24847/25000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((400 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12423524847/250000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-24847/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c401 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((401 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-829941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29969807/10000000 : ℚ) : ℝ) ≤ Real.log ((401 : ℕ)) / 2 := by
    have h := (log_br_401).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((401 : ℕ)) / 2 ≤ ((11987923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_401).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -199203/312500) (δ := 963/100000000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t401 : ((-414478415607/10000000000000 : ℚ) : ℝ) ≤ stT385o2 401 := by
  have hc : ((-829991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((401 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-414478415607/10000000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-829991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c402 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((402 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-479041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1499113/500000 : ℚ) : ℝ) ≤ Real.log ((402 : ℕ)) / 2 := by
    have h := (log_br_402).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((402 : ℕ)) / 2 ≤ ((59964521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_402).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1035179/2000000) (δ := 973/100000000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t402 : ((-47789806341/2000000000000 : ℚ) : ℝ) ≤ stT385o2 402 := by
  have hc : ((-479091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((402 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47789806341/2000000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-479091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c403 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((403 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-10647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11997873/4000000 : ℚ) : ℝ) ≤ Real.log ((403 : ℕ)) / 2 := by
    have h := (log_br_403).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((403 : ℕ)) / 2 ≤ ((29994683/10000000 : ℚ) : ℝ) := by
    have h := (log_br_403).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3980229/10000000) (δ := 9673/1000000000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t403 : ((-41532089/39062500000 : ℚ) : ℝ) ≤ stT385o2 403 := by
  have hc : ((-667/31250 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((403 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41532089/39062500000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-667/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c404 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((404 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((440161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15003537/5000000 : ℚ) : ℝ) ≤ Real.log ((404 : ℕ)) / 2 := by
    have h := (log_br_404).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((404 : ℕ)) / 2 ≤ ((60014149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_404).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2787547/10000000) (δ := 9723/1000000000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t404 : ((109481572249/5000000000000 : ℚ) : ℝ) ≤ stT385o2 404 := by
  have hc : ((440111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((404 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109481572249/5000000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((440111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c405 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((405 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((802621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6003887/2000000 : ℚ) : ℝ) ≤ Real.log ((405 : ℕ)) / 2 := by
    have h := (log_br_405).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((405 : ℕ)) / 2 ≤ ((60038871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_405).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1597801/10000000) (δ := 963/100000000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t405 : ((398799937613/10000000000000 : ℚ) : ℝ) ≤ stT385o2 405 := by
  have hc : ((802571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((405 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((398799937613/10000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((802571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c406 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((406 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((986517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60063531/20000000 : ℚ) : ℝ) ≤ Real.log ((406 : ℕ)) / 2 := by
    have h := (log_br_406).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((406 : ℕ)) / 2 ≤ ((15015883/5000000 : ℚ) : ℝ) := by
    have h := (log_br_406).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -41099/1000000) (δ := 9773/1000000000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t406 : ((489574693897/10000000000000 : ℚ) : ℝ) ≤ stT385o2 406 := by
  have hc : ((986467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((406 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((489574693897/10000000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((986467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c407 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((407 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((952591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60088131/20000000 : ℚ) : ℝ) ≤ Real.log ((407 : ℕ)) / 2 := by
    have h := (log_br_407).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((407 : ℕ)) / 2 ≤ ((15022033/5000000 : ℚ) : ℝ) := by
    have h := (log_br_407).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 154577/2000000) (δ := 9773/1000000000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t407 : ((472156475421/10000000000000 : ℚ) : ℝ) ≤ stT385o2 407 := by
  have hc : ((952541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((407 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((472156475421/10000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((952541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c408 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((408 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((709823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60112671/20000000 : ℚ) : ℝ) ≤ Real.log ((408 : ℕ)) / 2 := by
    have h := (log_br_408).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((408 : ℕ)) / 2 ≤ ((1878521/625000 : ℚ) : ℝ) := by
    have h := (log_br_408).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 122117/625000) (δ := 121/12500000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t408 : ((351389448429/10000000000000 : ℚ) : ℝ) ≤ stT385o2 408 := by
  have hc : ((709773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((408 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((351389448429/10000000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((709773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c409 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((409 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((12507/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60137151/20000000 : ℚ) : ℝ) ≤ Real.log ((409 : ℕ)) / 2 := by
    have h := (log_br_409).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((409 : ℕ)) / 2 ≤ ((939643/312500 : ℚ) : ℝ) := by
    have h := (log_br_409).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 782993/2500000) (δ := 121/12500000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t409 : ((309166117/20000000000 : ℚ) : ℝ) ≤ stT385o2 409 := by
  have hc : ((2501/8000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((409 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((309166117/20000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((2501/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c410 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((410 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-37873/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60161571/20000000 : ℚ) : ℝ) ≤ Real.log ((410 : ℕ)) / 2 := by
    have h := (log_br_410).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((410 : ℕ)) / 2 ≤ ((15040393/5000000 : ℚ) : ℝ) := by
    have h := (log_br_410).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 861437/2000000) (δ := 9773/1000000000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t410 : ((-7484128983/1000000000000 : ℚ) : ℝ) ≤ stT385o2 410 := by
  have hc : ((-75771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((410 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7484128983/1000000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-75771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c411 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((411 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-581871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15046483/5000000 : ℚ) : ℝ) ≤ Real.log ((411 : ℕ)) / 2 := by
    have h := (log_br_411).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((411 : ℕ)) / 2 ≤ ((60185933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_411).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2739779/5000000) (δ := 9723/1000000000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t411 : ((-17940042509/625000000000 : ℚ) : ℝ) ≤ stT385o2 411 := by
  have hc : ((-581921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((411 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17940042509/625000000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-581921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c412 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((412 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-886081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60210233/20000000 : ℚ) : ℝ) ≤ Real.log ((412 : ℕ)) / 2 := by
    have h := (log_br_412).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((412 : ℕ)) / 2 ≤ ((30105117/10000000 : ℚ) : ℝ) := by
    have h := (log_br_412).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6649043/10000000) (δ := 489/50000000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t412 : ((-87313145823/2000000000000 : ℚ) : ℝ) ≤ stT385o2 412 := by
  have hc : ((-886131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((412 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87313145823/2000000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-886131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c413 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((413 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-999883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2409379/800000 : ℚ) : ℝ) ≤ Real.log ((413 : ℕ)) / 2 := by
    have h := (log_br_413).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((413 : ℕ)) / 2 ≤ ((15058619/5000000 : ℚ) : ℝ) := by
    have h := (log_br_413).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 781569/1000000) (δ := 9773/1000000000) (ψ := 281281/1000000) 385 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t413 : ((-123008757861/2500000000000 : ℚ) : ℝ) ≤ stT385o2 413 := by
  have hc : ((-999933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((413 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123008757861/2500000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-999933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c414 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((414 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-900349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60258659/20000000 : ℚ) : ℝ) ≤ Real.log ((414 : ℕ)) / 2 := by
    have h := (log_br_414).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((414 : ℕ)) / 2 ≤ ((3012933/1000000 : ℚ) : ℝ) := by
    have h := (log_br_414).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6728419/10000000) (δ := 9773/1000000000) (ψ := 281281/1000000) 385 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t414 : ((-221261349063/5000000000000 : ℚ) : ℝ) ≤ stT385o2 414 := by
  have hc : ((-900399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((414 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221261349063/5000000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-900399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c415 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((415 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-610067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12056557/4000000 : ℚ) : ℝ) ≤ Real.log ((415 : ℕ)) / 2 := by
    have h := (log_br_415).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((415 : ℕ)) / 2 ≤ ((30141393/10000000 : ℚ) : ℝ) := by
    have h := (log_br_415).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1113471/2000000) (δ := 9673/1000000000) (ψ := 281281/1000000) 385 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t415 : ((-299494843077/10000000000000 : ℚ) : ℝ) ≤ stT385o2 415 := by
  have hc : ((-610117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((415 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-299494843077/10000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-610117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c416 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((416 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-191663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15076713/5000000 : ℚ) : ℝ) ≤ Real.log ((416 : ℕ)) / 2 := by
    have h := (log_br_416).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((416 : ℕ)) / 2 ≤ ((60306853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_416).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4409131/10000000) (δ := 9823/1000000000) (ψ := 281281/1000000) 385 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t416 : ((-93995158483/10000000000000 : ℚ) : ℝ) ≤ stT385o2 416 := by
  have hc : ((-191713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((416 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93995158483/10000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-191713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c417 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((417 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((66523/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30165431/10000000 : ℚ) : ℝ) ≤ Real.log ((417 : ℕ)) / 2 := by
    have h := (log_br_417).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((417 : ℕ)) / 2 ≤ ((60330863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_417).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3253649/10000000) (δ := 973/100000000) (ψ := 281281/1000000) 385 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t417 : ((32570324871/2500000000000 : ℚ) : ℝ) ≤ stT385o2 417 := by
  have hc : ((133021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((417 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).1
  have hw2 : ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((244851/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32570324871/2500000000000 : ℚ) : ℝ)
      = ((244851/5000000 : ℚ) : ℝ) * ((133021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c418 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((418 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((667177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30177407/10000000 : ℚ) : ℝ) ≤ Real.log ((418 : ℕ)) / 2 := by
    have h := (log_br_418).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((418 : ℕ)) / 2 ≤ ((12070963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_418).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2100959/10000000) (δ := 973/100000000) (ψ := 281281/1000000) 385 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t418 : ((65260364521/2000000000000 : ℚ) : ℝ) ≤ stT385o2 418 := by
  have hc : ((667127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((418 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65260364521/2000000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((667127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c419 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((419 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((464257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60378709/20000000 : ℚ) : ℝ) ≤ Real.log ((419 : ℕ)) / 2 := by
    have h := (log_br_419).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((419 : ℕ)) / 2 ≤ ((6037871/2000000 : ℚ) : ℝ) := by
    have h := (log_br_419).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -237753/2500000) (δ := 489/50000000) (ψ := 281281/1000000) 385 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t419 : ((28348965399/625000000000 : ℚ) : ℝ) ≤ stT385o2 419 := by
  have hc : ((58029/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((419 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28348965399/625000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((58029/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c420 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((420 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((498461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60402547/20000000 : ℚ) : ℝ) ≤ Real.log ((420 : ℕ)) / 2 := by
    have h := (log_br_420).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((420 : ℕ)) / 2 ≤ ((15100637/5000000 : ℚ) : ℝ) := by
    have h := (log_br_420).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 196191/10000000) (δ := 9773/1000000000) (ψ := 281281/1000000) 385 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t420 : ((1216059231/25000000000 : ℚ) : ℝ) ≤ stT385o2 420 := by
  have hc : ((124609/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((420 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1216059231/25000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((124609/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c421 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((421 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((6877/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7553291/2500000 : ℚ) : ℝ) ≤ Real.log ((421 : ℕ)) / 2 := by
    have h := (log_br_421).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((421 : ℕ)) / 2 ≤ ((60426329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_421).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 335163/2500000) (δ := 963/100000000) (ψ := 281281/1000000) 385 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t421 : ((1675724271/40000000000 : ℚ) : ℝ) ≤ stT385o2 421 := by
  have hc : ((34383/40000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((421 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1675724271/40000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((34383/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c422 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((422 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((546207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60450053/20000000 : ℚ) : ℝ) ≤ Real.log ((422 : ℕ)) / 2 := by
    have h := (log_br_422).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((422 : ℕ)) / 2 ≤ ((30225027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_422).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1241209/5000000) (δ := 489/50000000) (ψ := 281281/1000000) 385 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t422 : ((33233107293/1250000000000 : ℚ) : ℝ) ≤ stT385o2 422 := by
  have hc : ((546157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((422 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33233107293/1250000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((546157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c423 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((423 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((30479/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60473721/20000000 : ℚ) : ℝ) ≤ Real.log ((423 : ℕ)) / 2 := by
    have h := (log_br_423).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((423 : ℕ)) / 2 ≤ ((30236861/10000000 : ℚ) : ℝ) := by
    have h := (log_br_423).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 11317/31250) (δ := 9673/1000000000) (ψ := 281281/1000000) 385 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t423 : ((3703324941/625000000000 : ℚ) : ℝ) ≤ stT385o2 423 := by
  have hc : ((60933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((423 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3703324941/625000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((60933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c424 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((424 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-163123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30248667/10000000 : ℚ) : ℝ) ≤ Real.log ((424 : ℕ)) / 2 := by
    have h := (log_br_424).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((424 : ℕ)) / 2 ≤ ((12099467/4000000 : ℚ) : ℝ) := by
    have h := (log_br_424).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 594727/1250000) (δ := 973/100000000) (ψ := 281281/1000000) 385 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t424 : ((-19807921041/1250000000000 : ℚ) : ℝ) ≤ stT385o2 424 := by
  have hc : ((-40787/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((424 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19807921041/1250000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-40787/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c425 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((425 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-11053/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60520891/20000000 : ℚ) : ℝ) ≤ Real.log ((425 : ℕ)) / 2 := by
    have h := (log_br_425).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((425 : ℕ)) / 2 ≤ ((15130223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_425).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 736437/1250000) (δ := 9773/1000000000) (ψ := 281281/1000000) 385 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t425 : ((-10723759557/312500000000 : ℚ) : ℝ) ≤ stT385o2 425 := by
  have hc : ((-353721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((425 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10723759557/312500000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-353721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c426 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((426 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-945203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60544393/20000000 : ℚ) : ℝ) ≤ Real.log ((426 : ℕ)) / 2 := by
    have h := (log_br_426).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((426 : ℕ)) / 2 ≤ ((30272197/10000000 : ℚ) : ℝ) := by
    have h := (log_br_426).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 702253/1000000) (δ := 9673/1000000000) (ψ := 281281/1000000) 385 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t426 : ((-228988484503/5000000000000 : ℚ) : ℝ) ≤ stT385o2 426 := by
  have hc : ((-945253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((426 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228988484503/5000000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-945253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c427 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((427 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-198591/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((378549/125000 : ℚ) : ℝ) ≤ Real.log ((427 : ℕ)) / 2 := by
    have h := (log_br_427).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((427 : ℕ)) / 2 ≤ ((60567841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_427).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3778523/5000000) (δ := 9737/1000000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t427 : ((-48054888167/1000000000000 : ℚ) : ℝ) ≤ stT385o2 427 := by
  have hc : ((-198601/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((427 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48054888167/1000000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-198601/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c428 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((428 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-842413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60591231/20000000 : ℚ) : ℝ) ≤ Real.log ((428 : ℕ)) / 2 := by
    have h := (log_br_428).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((428 : ℕ)) / 2 ≤ ((473369/156250 : ℚ) : ℝ) := by
    have h := (log_br_428).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3215677/5000000) (δ := 9787/1000000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t428 : ((-407220497847/10000000000000 : ℚ) : ℝ) ≤ stT385o2 428 := by
  have hc : ((-842463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((428 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-407220497847/10000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-842463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c429 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((429 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-524807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60614569/20000000 : ℚ) : ℝ) ≤ Real.log ((429 : ℕ)) / 2 := by
    have h := (log_br_429).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((429 : ℕ)) / 2 ≤ ((6061457/2000000 : ℚ) : ℝ) := by
    have h := (log_br_429).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5308213/10000000) (δ := 9687/1000000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t429 : ((-50680716777/2000000000000 : ℚ) : ℝ) ≤ stT385o2 429 := by
  have hc : ((-524857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((429 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50680716777/2000000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-524857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c430 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((430 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-52051/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15159463/5000000 : ℚ) : ℝ) ≤ Real.log ((430 : ℕ)) / 2 := by
    have h := (log_br_430).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((430 : ℕ)) / 2 ≤ ((60637853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_430).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4187719/10000000) (δ := 2429/250000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t430 : ((-6278321617/1250000000000 : ℚ) : ℝ) ≤ stT385o2 430 := by
  have hc : ((-13019/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((430 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6278321617/1250000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-13019/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c431 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((431 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((336171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1516527/500000 : ℚ) : ℝ) ≤ Real.log ((431 : ℕ)) / 2 := by
    have h := (log_br_431).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((431 : ℕ)) / 2 ≤ ((60661081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_431).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3069871/10000000) (δ := 9737/1000000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t431 : ((161903771643/10000000000000 : ℚ) : ℝ) ≤ stT385o2 431 := by
  have hc : ((336121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((431 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161903771643/10000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((336121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c432 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((432 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((354813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12136851/4000000 : ℚ) : ℝ) ≤ Real.log ((432 : ℕ)) / 2 := by
    have h := (log_br_432).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((432 : ℕ)) / 2 ≤ ((1896383/625000 : ℚ) : ℝ) := by
    have h := (log_br_432).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -977287/5000000) (δ := 9787/1000000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t432 : ((341394753/10000000000 : ℚ) : ℝ) ≤ stT385o2 432 := by
  have hc : ((88697/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((432 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((341394753/10000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((88697/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c433 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((433 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((5899/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60707377/20000000 : ℚ) : ℝ) ≤ Real.log ((433 : ℕ)) / 2 := by
    have h := (log_br_433).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((433 : ℕ)) / 2 ≤ ((30353689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_433).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -210457/2500000) (δ := 9687/1000000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t433 : ((45355621651/1000000000000 : ℚ) : ℝ) ≤ stT385o2 433 := by
  have hc : ((94379/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((433 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45355621651/1000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((94379/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c434 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((434 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((497123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12146089/4000000 : ℚ) : ℝ) ≤ Real.log ((434 : ℕ)) / 2 := by
    have h := (log_br_434).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((434 : ℕ)) / 2 ≤ ((30365223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_434).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 268319/10000000) (δ := 4883/500000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t434 : ((23861449647/500000000000 : ℚ) : ℝ) ≤ stT385o2 434 := by
  have hc : ((248549/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((434 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23861449647/500000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((248549/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c435 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((435 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((852333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3037673/1000000 : ℚ) : ℝ) ≤ Real.log ((435 : ℕ)) / 2 := by
    have h := (log_br_435).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((435 : ℕ)) / 2 ≤ ((60753461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_435).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 343979/2500000) (δ := 2429/250000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t435 : ((408638164029/10000000000000 : ℚ) : ℝ) ≤ stT385o2 435 := by
  have hc : ((852283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((435 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((408638164029/10000000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((852283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c436 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((436 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((109339/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30388211/10000000 : ℚ) : ℝ) ≤ Real.log ((436 : ℕ)) / 2 := by
    have h := (log_br_436).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((436 : ℕ)) / 2 ≤ ((60776423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_436).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1240481/5000000) (δ := 1227/125000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t436 : ((52359079377/2000000000000 : ℚ) : ℝ) ≤ stT385o2 436 := by
  have hc : ((109329/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((436 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52359079377/2000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((109329/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c437 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((437 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((136981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60799331/20000000 : ℚ) : ℝ) ≤ Real.log ((437 : ℕ)) / 2 := by
    have h := (log_br_437).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((437 : ℕ)) / 2 ≤ ((15199833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_437).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1791729/5000000) (δ := 4833/500000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t437 : ((16375715221/2500000000000 : ℚ) : ℝ) ≤ stT385o2 437 := by
  have hc : ((136931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((437 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16375715221/2500000000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((136931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c438 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((438 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-149003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60822189/20000000 : ℚ) : ℝ) ≤ Real.log ((438 : ℕ)) / 2 := by
    have h := (log_br_438).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((438 : ℕ)) / 2 ≤ ((6082219/2000000 : ℚ) : ℝ) := by
    have h := (log_br_438).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4683499/10000000) (δ := 4883/500000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t438 : ((-17802102483/1250000000000 : ℚ) : ℝ) ≤ stT385o2 438 := by
  have hc : ((-37257/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((438 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17802102483/1250000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-37257/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c439 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((439 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-168867/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30422497/10000000 : ℚ) : ℝ) ≤ Real.log ((439 : ℕ)) / 2 := by
    have h := (log_br_439).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((439 : ℕ)) / 2 ≤ ((12168999/4000000 : ℚ) : ℝ) := by
    have h := (log_br_439).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 578099/1000000) (δ := 9637/1000000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t439 : ((-80601794483/2500000000000 : ℚ) : ℝ) ≤ stT385o2 439 := by
  have hc : ((-337759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((439 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80601794483/2500000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-337759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c440 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((440 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-231113/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60867747/20000000 : ℚ) : ℝ) ≤ Real.log ((440 : ℕ)) / 2 := by
    have h := (log_br_440).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((440 : ℕ)) / 2 ≤ ((15216937/5000000 : ℚ) : ℝ) := by
    have h := (log_br_440).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3437989/5000000) (δ := 4833/500000000) (ψ := 281281/1000000) 385 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t440 : ((-55092460933/1250000000000 : ℚ) : ℝ) ≤ stT385o2 440 := by
  have hc : ((-462251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((440 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55092460933/1250000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-462251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c441 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((441 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-124869/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3805653/1250000 : ℚ) : ℝ) ≤ Real.log ((441 : ℕ)) / 2 := by
    have h := (log_br_441).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((441 : ℕ)) / 2 ≤ ((60890449/20000000 : ℚ) : ℝ) := by
    have h := (log_br_441).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -15479/20000) (δ := 9809/1000000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t441 : ((-237857880691/5000000000000 : ℚ) : ℝ) ≤ stT385o2 441 := by
  have hc : ((-499501/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((441 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237857880691/5000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-499501/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c442 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((442 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-11077/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30456549/10000000 : ℚ) : ℝ) ≤ Real.log ((442 : ℕ)) / 2 := by
    have h := (log_br_442).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((442 : ℕ)) / 2 ≤ ((60913099/20000000 : ℚ) : ℝ) := by
    have h := (log_br_442).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1662367/2500000) (δ := 609/62500000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t442 : ((-10538188973/250000000000 : ℚ) : ℝ) ≤ stT385o2 442 := by
  have hc : ((-88621/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((442 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10538188973/250000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-88621/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c443 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((443 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-304167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60935697/20000000 : ℚ) : ℝ) ≤ Real.log ((443 : ℕ)) / 2 := by
    have h := (log_br_443).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((443 : ℕ)) / 2 ≤ ((30467849/10000000 : ℚ) : ℝ) := by
    have h := (log_br_443).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5561891/10000000) (δ := 4897/500000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t443 : ((-451644319/15625000000 : ℚ) : ℝ) ≤ stT385o2 443 := by
  have hc : ((-9506/15625 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((443 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-451644319/15625000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-9506/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c444 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((444 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-218143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12191649/4000000 : ℚ) : ℝ) ≤ Real.log ((444 : ℕ)) / 2 := by
    have h := (log_br_444).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((444 : ℕ)) / 2 ≤ ((30479123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_444).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4476769/10000000) (δ := 9659/1000000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t444 : ((-103549815747/10000000000000 : ℚ) : ℝ) ≤ stT385o2 444 := by
  have hc : ((-218193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((444 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103549815747/10000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-218193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c445 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((445 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((42309/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30490371/10000000 : ℚ) : ℝ) ≤ Real.log ((445 : ℕ)) / 2 := by
    have h := (log_br_445).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((445 : ℕ)) / 2 ≤ ((60980743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_445).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3394101/10000000) (δ := 9709/1000000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t445 : ((4010325891/400000000000 : ℚ) : ℝ) ≤ stT385o2 445 := by
  have hc : ((42299/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((445 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4010325891/400000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((42299/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c446 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((446 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((601407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61003189/20000000 : ℚ) : ℝ) ≤ Real.log ((446 : ℕ)) / 2 := by
    have h := (log_br_446).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((446 : ℕ)) / 2 ≤ ((6100319/2000000 : ℚ) : ℝ) := by
    have h := (log_br_446).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2313839/10000000) (δ := 9659/1000000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t446 : ((284750357141/10000000000000 : ℚ) : ℝ) ≤ stT385o2 446 := by
  have hc : ((601357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((446 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284750357141/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((601357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c447 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((447 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((110031/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12205117/4000000 : ℚ) : ℝ) ≤ Real.log ((447 : ℕ)) / 2 := by
    have h := (log_br_447).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((447 : ℕ)) / 2 ≤ ((30512793/10000000 : ℚ) : ℝ) := by
    have h := (log_br_447).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1236031/10000000) (δ := 4897/500000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t447 : ((208159345317/5000000000000 : ℚ) : ℝ) ≤ stT385o2 447 := by
  have hc : ((440099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((447 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208159345317/5000000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((440099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c448 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((448 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((498969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15261983/5000000 : ℚ) : ℝ) ≤ Real.log ((448 : ℕ)) / 2 := by
    have h := (log_br_448).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((448 : ℕ)) / 2 ≤ ((61047933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_448).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -80291/5000000) (δ := 2411/250000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t448 : ((184162959/3906250000 : ℚ) : ℝ) ≤ stT385o2 448 := by
  have hc : ((15592/15625 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((448 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184162959/3906250000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((15592/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c449 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((449 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((116767/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15267557/5000000 : ℚ) : ℝ) ≤ Real.log ((449 : ℕ)) / 2 := by
    have h := (log_br_449).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((449 : ℕ)) / 2 ≤ ((61070229/20000000 : ℚ) : ℝ) := by
    have h := (log_br_449).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 912413/10000000) (δ := 2411/250000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t449 : ((220411135947/5000000000000 : ℚ) : ℝ) ≤ stT385o2 449 := by
  have hc : ((467043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((449 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220411135947/5000000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((467043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c450 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((450 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((350777/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2443699/800000 : ℚ) : ℝ) ≤ Real.log ((450 : ℕ)) / 2 := by
    have h := (log_br_450).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((450 : ℕ)) / 2 ≤ ((15273119/5000000 : ℚ) : ℝ) := by
    have h := (log_br_450).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 39661/200000) (δ := 4847/500000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t450 : ((1291764811/39062500000 : ℚ) : ℝ) ≤ stT385o2 450 := by
  have hc : ((10961/15625 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((450 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1291764811/39062500000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((10961/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c451 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((451 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((171573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61114673/20000000 : ℚ) : ℝ) ≤ Real.log ((451 : ℕ)) / 2 := by
    have h := (log_br_451).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((451 : ℕ)) / 2 ≤ ((30557337/10000000 : ℚ) : ℝ) := by
    have h := (log_br_451).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3051329/10000000) (δ := 4897/500000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t451 : ((20194673447/1250000000000 : ℚ) : ℝ) ≤ stT385o2 451 := by
  have hc : ((42887/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((451 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20194673447/1250000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((42887/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c452 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((452 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-76011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61136821/20000000 : ℚ) : ℝ) ≤ Real.log ((452 : ℕ)) / 2 := by
    have h := (log_br_452).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((452 : ℕ)) / 2 ≤ ((30568411/10000000 : ℚ) : ℝ) := by
    have h := (log_br_452).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4117201/10000000) (δ := 9659/1000000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t452 : ((-35776128021/10000000000000 : ℚ) : ℝ) ≤ stT385o2 452 := by
  have hc : ((-76061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((452 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35776128021/10000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-76061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c453 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((453 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-1923/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61158921/20000000 : ℚ) : ℝ) ≤ Real.log ((453 : ℕ)) / 2 := by
    have h := (log_br_453).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((453 : ℕ)) / 2 ≤ ((30579461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_453).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1295191/2500000) (δ := 4897/500000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t453 : ((-282374441/12500000000 : ℚ) : ℝ) ≤ stT385o2 453 := by
  have hc : ((-601/1250 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((453 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282374441/12500000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-601/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c454 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((454 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-159841/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61180971/20000000 : ℚ) : ℝ) ≤ Real.log ((454 : ℕ)) / 2 := by
    have h := (log_br_454).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((454 : ℕ)) / 2 ≤ ((15295243/5000000 : ℚ) : ℝ) := by
    have h := (log_br_454).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 9753/15625) (δ := 4847/500000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t454 : ((-18755477681/500000000000 : ℚ) : ℝ) ≤ stT385o2 454 := by
  have hc : ((-159851/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((454 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18755477681/500000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-159851/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c455 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((455 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-48781/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30601487/10000000 : ℚ) : ℝ) ≤ Real.log ((455 : ℕ)) / 2 := by
    have h := (log_br_455).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((455 : ℕ)) / 2 ≤ ((2448119/800000 : ℚ) : ℝ) := by
    have h := (log_br_455).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3650407/5000000) (δ := 9709/1000000000) (ψ := 281281/1000000) 385 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t455 : ((-5717523767/125000000000 : ℚ) : ℝ) ≤ stT385o2 455 := by
  have hc : ((-97567/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((455 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5717523767/125000000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-97567/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c456 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((456 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-489899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1913279/625000 : ℚ) : ℝ) ≤ Real.log ((456 : ℕ)) / 2 := by
    have h := (log_br_456).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((456 : ℕ)) / 2 ≤ ((61224929/20000000 : ℚ) : ℝ) := by
    have h := (log_br_456).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7350613/10000000) (δ := 4851/500000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t456 : ((-57356994933/1250000000000 : ℚ) : ℝ) ≤ stT385o2 456 := by
  have hc : ((-122481/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((456 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57356994933/1250000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-122481/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c457 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((457 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-812121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61246833/20000000 : ℚ) : ℝ) ≤ Real.log ((457 : ℕ)) / 2 := by
    have h := (log_br_457).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((457 : ℕ)) / 2 ≤ ((30623417/10000000 : ℚ) : ℝ) := by
    have h := (log_br_457).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1259287/2000000) (δ := 1219/125000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t457 : ((-379918162551/10000000000000 : ℚ) : ℝ) ≤ stT385o2 457 := by
  have hc : ((-812171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((457 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-379918162551/10000000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-812171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c458 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((458 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-62869/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61268691/20000000 : ℚ) : ℝ) ≤ Real.log ((458 : ℕ)) / 2 := by
    have h := (log_br_458).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((458 : ℕ)) / 2 ≤ ((15317173/5000000 : ℚ) : ℝ) := by
    have h := (log_br_458).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2622259/5000000) (δ := 9801/1000000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t458 : ((-11751887227/500000000000 : ℚ) : ℝ) ≤ stT385o2 458 := by
  have hc : ((-251501/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((458 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11751887227/500000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-251501/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c459 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((459 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-1671/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30645251/10000000 : ℚ) : ℝ) ≤ Real.log ((459 : ℕ)) / 2 := by
    have h := (log_br_459).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((459 : ℕ)) / 2 ≤ ((61290503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_459).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -262179/625000) (δ := 9651/1000000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t459 : ((-24970313217/5000000000000 : ℚ) : ℝ) ≤ stT385o2 459 := by
  have hc : ((-53497/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((459 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24970313217/5000000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-53497/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c460 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((460 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((306743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7664033/2500000 : ℚ) : ℝ) ≤ Real.log ((460 : ℕ)) / 2 := by
    have h := (log_br_460).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((460 : ℕ)) / 2 ≤ ((12262453/4000000 : ℚ) : ℝ) := by
    have h := (log_br_460).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -196723/625000) (δ := 4851/500000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t460 : ((35749056159/2500000000000 : ℚ) : ℝ) ≤ stT385o2 460 := by
  have hc : ((306693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((460 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35749056159/2500000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((306693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c461 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((461 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((333361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3066699/1000000 : ℚ) : ℝ) ≤ Real.log ((461 : ℕ)) / 2 := by
    have h := (log_br_461).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((461 : ℕ)) / 2 ≤ ((61333981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_461).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -420497/2000000) (δ := 9751/1000000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t461 : ((9703119291/312500000000 : ℚ) : ℝ) ≤ stT385o2 461 := by
  have hc : ((41667/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((461 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9703119291/312500000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((41667/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c462 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((462 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((455749/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((479341/156250 : ℚ) : ℝ) ≤ Real.log ((462 : ℕ)) / 2 := by
    have h := (log_br_462).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((462 : ℕ)) / 2 ≤ ((61355649/20000000 : ℚ) : ℝ) := by
    have h := (log_br_462).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1059713/10000000) (δ := 4851/500000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t462 : ((26502743151/625000000000 : ℚ) : ℝ) ≤ stT385o2 462 := by
  have hc : ((113931/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((462 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26502743151/625000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((113931/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c463 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((463 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((999971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6137727/2000000 : ℚ) : ℝ) ≤ Real.log ((463 : ℕ)) / 2 := by
    have h := (log_br_463).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((463 : ℕ)) / 2 ≤ ((61377271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_463).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -9577/5000000) (δ := 9651/1000000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t463 : ((464702285619/10000000000000 : ℚ) : ℝ) ≤ stT385o2 463 := by
  have hc : ((999921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((463 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((464702285619/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((999921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c464 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((464 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((229513/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12279769/4000000 : ℚ) : ℝ) ≤ Real.log ((464 : ℕ)) / 2 := by
    have h := (log_br_464).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((464 : ℕ)) / 2 ≤ ((30699423/10000000 : ℚ) : ℝ) := by
    have h := (log_br_464).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1019143/10000000) (δ := 9701/1000000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t464 : ((106542853119/2500000000000 : ℚ) : ℝ) ≤ stT385o2 464 := by
  have hc : ((459001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((464 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106542853119/2500000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((459001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c465 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((465 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((680691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30710187/10000000 : ℚ) : ℝ) ≤ Real.log ((465 : ℕ)) / 2 := by
    have h := (log_br_465).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((465 : ℕ)) / 2 ≤ ((491363/160000 : ℚ) : ℝ) := by
    have h := (log_br_465).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1027613/5000000) (δ := 9651/1000000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t465 : ((157819548029/5000000000000 : ℚ) : ℝ) ≤ stT385o2 465 := by
  have hc : ((680641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((465 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157819548029/5000000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((680641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c466 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((466 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((328937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((960029/312500 : ℚ) : ℝ) ≤ Real.log ((466 : ℕ)) / 2 := by
    have h := (log_br_466).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((466 : ℕ)) / 2 ≤ ((61441857/20000000 : ℚ) : ℝ) := by
    have h := (log_br_466).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3089047/10000000) (δ := 4851/500000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t466 : ((152353942767/10000000000000 : ℚ) : ℝ) ≤ stT385o2 466 := by
  have hc : ((328887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((466 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152353942767/10000000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((328887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c467 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((467 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-19347/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15365823/5000000 : ℚ) : ℝ) ≤ Real.log ((467 : ℕ)) / 2 := by
    have h := (log_br_467).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((467 : ℕ)) / 2 ≤ ((61463293/20000000 : ℚ) : ℝ) := by
    have h := (log_br_467).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 824131/2000000) (δ := 9751/1000000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t467 : ((-3583404731/1000000000000 : ℚ) : ℝ) ≤ stT385o2 467 := by
  have hc : ((-38719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((467 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3583404731/1000000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-38719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c468 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((468 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-23497/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30742341/10000000 : ℚ) : ℝ) ≤ Real.log ((468 : ℕ)) / 2 := by
    have h := (log_br_468).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((468 : ℕ)) / 2 ≤ ((61484683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_468).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 160939/312500) (δ := 4901/500000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t468 : ((-21725334749/1000000000000 : ℚ) : ℝ) ≤ stT385o2 468 := by
  have hc : ((-46999/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((468 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21725334749/1000000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-46999/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c469 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((469 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-391699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61506027/20000000 : ℚ) : ℝ) ≤ Real.log ((469 : ℕ)) / 2 := by
    have h := (log_br_469).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((469 : ℕ)) / 2 ≤ ((15376507/5000000 : ℚ) : ℝ) := by
    have h := (log_br_469).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6177277/10000000) (δ := 9801/1000000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t469 : ((-22610211349/625000000000 : ℚ) : ℝ) ≤ stT385o2 469 := by
  have hc : ((-97931/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((469 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22610211349/625000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-97931/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c470 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((470 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-120777/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30763663/10000000 : ℚ) : ℝ) ≤ Real.log ((470 : ℕ)) / 2 := by
    have h := (log_br_470).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((470 : ℕ)) / 2 ≤ ((61527327/20000000 : ℚ) : ℝ) := by
    have h := (log_br_470).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7202291/10000000) (δ := 9651/1000000000) (ψ := 281281/1000000) 385 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t470 : ((-111426413189/2500000000000 : ℚ) : ℝ) ≤ stT385o2 470 := by
  have hc : ((-483133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((470 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111426413189/2500000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-483133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c471 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((471 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-989/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3077429/1000000 : ℚ) : ℝ) ≤ Real.log ((471 : ℕ)) / 2 := by
    have h := (log_br_471).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((471 : ℕ)) / 2 ≤ ((61548581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_471).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -935353/1250000) (δ := 1959/200000000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t471 : ((-1139326257/25000000000 : ℚ) : ℝ) ≤ stT385o2 471 := by
  have hc : ((-19781/20000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((471 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1139326257/25000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-19781/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c472 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((472 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-106123/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61569789/20000000 : ℚ) : ℝ) ≤ Real.log ((472 : ℕ)) / 2 := by
    have h := (log_br_472).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((472 : ℕ)) / 2 ≤ ((6156979/2000000 : ℚ) : ℝ) := by
    have h := (log_br_472).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -323107/500000) (δ := 613/62500000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t472 : ((-381640783/9765625000 : ℚ) : ℝ) ≤ stT385o2 472 := by
  have hc : ((-424517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((472 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-381640783/9765625000 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-424517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c473 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((473 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-570121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61590953/20000000 : ℚ) : ℝ) ≤ Real.log ((473 : ℕ)) / 2 := by
    have h := (log_br_473).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((473 : ℕ)) / 2 ≤ ((30795477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_473).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5443623/10000000) (δ := 1929/200000000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t473 : ((-262165195971/10000000000000 : ℚ) : ℝ) ≤ stT385o2 473 := by
  have hc : ((-570171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((473 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).2
  have h0 : (0:ℝ) ≤ ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262165195971/10000000000000 : ℚ) : ℝ)
      = ((459801/10000000 : ℚ) : ℝ) * ((-570171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c474 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((474 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-4969/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61612073/20000000 : ℚ) : ℝ) ≤ Real.log ((474 : ℕ)) / 2 := by
    have h := (log_br_474).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((474 : ℕ)) / 2 ≤ ((30806037/10000000 : ℚ) : ℝ) := by
    have h := (log_br_474).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4427223/10000000) (δ := 1929/200000000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t474 : ((-2282915349/250000000000 : ℚ) : ℝ) ≤ stT385o2 474 := by
  have hc : ((-19881/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((474 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).2
  have h0 : (0:ℝ) ≤ ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2282915349/250000000000 : ℚ) : ℝ)
      = ((114829/2500000 : ℚ) : ℝ) * ((-19881/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c475 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((475 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((40831/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15408287/5000000 : ℚ) : ℝ) ≤ Real.log ((475 : ℕ)) / 2 := by
    have h := (log_br_475).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((475 : ℕ)) / 2 ≤ ((61633149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_475).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3412989/10000000) (δ := 1959/200000000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t475 : ((18729940251/2000000000000 : ℚ) : ℝ) ≤ stT385o2 475 := by
  have hc : ((40821/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((475 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18729940251/2000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((40821/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c476 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((476 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((286609/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30827089/10000000 : ℚ) : ℝ) ≤ Real.log ((476 : ℕ)) / 2 := by
    have h := (log_br_476).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((476 : ℕ)) / 2 ≤ ((61654179/20000000 : ℚ) : ℝ) := by
    have h := (log_br_476).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -60023/250000) (δ := 1939/200000000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t476 : ((16419436227/625000000000 : ℚ) : ℝ) ≤ stT385o2 476 := by
  have hc : ((35823/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((476 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16419436227/625000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((35823/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c477 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((477 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((53073/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15418791/5000000 : ℚ) : ℝ) ≤ Real.log ((477 : ℕ)) / 2 := by
    have h := (log_br_477).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((477 : ℕ)) / 2 ≤ ((12335033/4000000 : ℚ) : ℝ) := by
    have h := (log_br_477).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1390969/10000000) (δ := 1959/200000000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t477 : ((48597995053/1250000000000 : ℚ) : ℝ) ≤ stT385o2 477 := by
  have hc : ((424559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((477 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48597995053/1250000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((424559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c478 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((478 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((988283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61696107/20000000 : ℚ) : ℝ) ≤ Real.log ((478 : ℕ)) / 2 := by
    have h := (log_br_478).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((478 : ℕ)) / 2 ≤ ((15424027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_478).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -383087/10000000) (δ := 1949/200000000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t478 : ((452006903637/10000000000000 : ℚ) : ℝ) ≤ stT385o2 478 := by
  have hc : ((988233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((478 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).1
  have hw2 : ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((457389/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((452006903637/10000000000000 : ℚ) : ℝ)
      = ((457389/10000000 : ℚ) : ℝ) * ((988233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c479 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((479 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((969147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12343401/4000000 : ℚ) : ℝ) ≤ Real.log ((479 : ℕ)) / 2 := by
    have h := (log_br_479).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((479 : ℕ)) / 2 ≤ ((30858503/10000000 : ℚ) : ℝ) := by
    have h := (log_br_479).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 62263/1000000) (δ := 613/62500000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t479 : ((442791079367/10000000000000 : ℚ) : ℝ) ≤ stT385o2 479 := by
  have hc : ((969097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((479 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).1
  have hw2 : ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((456911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((442791079367/10000000000000 : ℚ) : ℝ)
      = ((456911/10000000 : ℚ) : ℝ) * ((969097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c480 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((480 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((795763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61737861/20000000 : ℚ) : ℝ) ≤ Real.log ((480 : ℕ)) / 2 := by
    have h := (log_br_480).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((480 : ℕ)) / 2 ≤ ((30868931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_480).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 65053/400000) (δ := 613/62500000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t480 : ((72638252631/2000000000000 : ℚ) : ℝ) ≤ stT385o2 480 := by
  have hc : ((795713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((480 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).1
  have hw2 : ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72638252631/2000000000000 : ℚ) : ℝ)
      = ((91287/2000000 : ℚ) : ℝ) * ((795713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c481 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((481 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((24829/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3859917/1250000 : ℚ) : ℝ) ≤ Real.log ((481 : ℕ)) / 2 := by
    have h := (log_br_481).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((481 : ℕ)) / 2 ≤ ((61758673/20000000 : ℚ) : ℝ) := by
    have h := (log_br_481).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1313927/5000000) (δ := 4829/500000000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t481 : ((565994547/25000000000 : ℚ) : ℝ) ≤ stT385o2 481 := by
  have hc : ((49653/100000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((481 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).1
  have hw2 : ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11399/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((565994547/25000000000 : ℚ) : ℝ)
      = ((11399/250000 : ℚ) : ℝ) * ((49653/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c482 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((482 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((23913/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61779441/20000000 : ℚ) : ℝ) ≤ Real.log ((482 : ℕ)) / 2 := by
    have h := (log_br_482).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((482 : ℕ)) / 2 ≤ ((30889721/10000000 : ℚ) : ℝ) := by
    have h := (log_br_482).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1813681/5000000) (δ := 1929/200000000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t482 : ((10887505761/2000000000000 : ℚ) : ℝ) ≤ stT385o2 482 := by
  have hc : ((23903/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((482 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10887505761/2000000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((23903/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c483 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((483 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-55099/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30900083/10000000 : ℚ) : ℝ) ≤ Real.log ((483 : ℕ)) / 2 := by
    have h := (log_br_483).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((483 : ℕ)) / 2 ≤ ((61800167/20000000 : ℚ) : ℝ) := by
    have h := (log_br_483).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4624753/10000000) (δ := 4879/500000000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t483 : ((-3134434593/250000000000 : ℚ) : ℝ) ≤ stT385o2 483 := by
  have hc : ((-55109/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((483 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).2
  have h0 : (0:ℝ) ≤ ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3134434593/250000000000 : ℚ) : ℝ)
      = ((56877/1250000 : ℚ) : ℝ) * ((-55109/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c484 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((484 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-313327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61820849/20000000 : ℚ) : ℝ) ≤ Real.log ((484 : ℕ)) / 2 := by
    have h := (log_br_484).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((484 : ℕ)) / 2 ≤ ((1236417/400000 : ℚ) : ℝ) := by
    have h := (log_br_484).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2810061/5000000) (δ := 1929/200000000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t484 : ((-8902056137/312500000000 : ℚ) : ℝ) ≤ stT385o2 484 := by
  have hc : ((-39169/62500 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((484 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).2
  have h0 : (0:ℝ) ≤ ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8902056137/312500000000 : ℚ) : ℝ)
      = ((227273/5000000 : ℚ) : ℝ) * ((-39169/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c485 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((485 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-439689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3865093/1250000 : ℚ) : ℝ) ≤ Real.log ((485 : ℕ)) / 2 := by
    have h := (log_br_485).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((485 : ℕ)) / 2 ≤ ((61841489/20000000 : ℚ) : ℝ) := by
    have h := (log_br_485).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3306687/5000000) (δ := 4829/500000000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t485 : ((-99832006989/2500000000000 : ℚ) : ℝ) ≤ stT385o2 485 := by
  have hc : ((-219857/250000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((485 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).2
  have h0 : (0:ℝ) ≤ ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99832006989/2500000000000 : ℚ) : ℝ)
      = ((454077/10000000 : ℚ) : ℝ) * ((-219857/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c486 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((486 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-995031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30931043/10000000 : ℚ) : ℝ) ≤ Real.log ((486 : ℕ)) / 2 := by
    have h := (log_br_486).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((486 : ℕ)) / 2 ≤ ((61862087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_486).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7604653/10000000) (δ := 4879/500000000) (ψ := 281281/1000000) 385 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t486 : ((-45137869241/1000000000000 : ℚ) : ℝ) ≤ stT385o2 486 := by
  have hc : ((-995081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((486 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45137869241/1000000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-995081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c487 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((487 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-38261/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61882641/20000000 : ℚ) : ℝ) ≤ Real.log ((487 : ℕ)) / 2 := by
    have h := (log_br_487).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((487 : ℕ)) / 2 ≤ ((30941321/10000000 : ℚ) : ℝ) := by
    have h := (log_br_487).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7114101/10000000) (δ := 2429/250000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t487 : ((-2167331109/50000000000 : ℚ) : ℝ) ≤ stT385o2 487 := by
  have hc : ((-38263/40000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((487 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2167331109/50000000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-38263/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c488 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((488 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-770719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30951577/10000000 : ℚ) : ℝ) ≤ Real.log ((488 : ℕ)) / 2 := by
    have h := (log_br_488).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((488 : ℕ)) / 2 ≤ ((12380631/4000000 : ℚ) : ℝ) := by
    have h := (log_br_488).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6126913/10000000) (δ := 4833/500000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t488 : ((-348910940151/10000000000000 : ℚ) : ℝ) ≤ stT385o2 488 := by
  have hc : ((-770769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((488 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-348910940151/10000000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-770769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c489 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((489 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-467023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7740453/2500000 : ℚ) : ℝ) ≤ Real.log ((489 : ℕ)) / 2 := by
    have h := (log_br_489).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((489 : ℕ)) / 2 ≤ ((495389/160000 : ℚ) : ℝ) := by
    have h := (log_br_489).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2570897/5000000) (δ := 4883/500000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t489 : ((-26402235471/1250000000000 : ℚ) : ℝ) ≤ stT385o2 489 := by
  have hc : ((-467073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((489 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26402235471/1250000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-467073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c490 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((490 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-92531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61944053/20000000 : ℚ) : ℝ) ≤ Real.log ((490 : ℕ)) / 2 := by
    have h := (log_br_490).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((490 : ℕ)) / 2 ≤ ((30972027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_490).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4158649/10000000) (δ := 9737/1000000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t490 : ((-20911918537/5000000000000 : ℚ) : ℝ) ≤ stT385o2 490 := by
  have hc : ((-92581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((490 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20911918537/5000000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-92581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c491 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((491 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((59067/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61964441/20000000 : ℚ) : ℝ) ≤ Real.log ((491 : ℕ)) / 2 := by
    have h := (log_br_491).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((491 : ℕ)) / 2 ≤ ((30982221/10000000 : ℚ) : ℝ) := by
    have h := (log_br_491).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -794369/2500000) (δ := 2429/250000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t491 : ((26652010701/2000000000000 : ℚ) : ℝ) ≤ stT385o2 491 := by
  have hc : ((59057/200000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((491 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).1
  have hw2 : ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451293/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26652010701/2000000000000 : ℚ) : ℝ)
      = ((451293/10000000 : ℚ) : ℝ) * ((59057/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c492 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((492 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((637667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61984787/20000000 : ℚ) : ℝ) ≤ Real.log ((492 : ℕ)) / 2 := by
    have h := (log_br_492).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((492 : ℕ)) / 2 ≤ ((15496197/5000000 : ℚ) : ℝ) := by
    have h := (log_br_492).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -87933/400000) (δ := 9637/1000000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t492 : ((143729711289/5000000000000 : ℚ) : ℝ) ≤ stT385o2 492 := by
  have hc : ((637617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((492 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143729711289/5000000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((637617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c493 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((493 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((110381/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62005091/20000000 : ℚ) : ℝ) ≤ Real.log ((493 : ℕ)) / 2 := by
    have h := (log_br_493).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((493 : ℕ)) / 2 ≤ ((15501273/5000000 : ℚ) : ℝ) := by
    have h := (log_br_493).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -244239/2000000) (δ := 9637/1000000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t493 : ((198840995123/5000000000000 : ℚ) : ℝ) ≤ stT385o2 493 := by
  have hc : ((441499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((493 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198840995123/5000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((441499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c494 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((494 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((995163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12405071/4000000 : ℚ) : ℝ) ≤ Real.log ((494 : ℕ)) / 2 := by
    have h := (log_br_494).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((494 : ℕ)) / 2 ≤ ((15506339/5000000 : ℚ) : ℝ) := by
    have h := (log_br_494).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -24599/1000000) (δ := 9637/1000000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t494 : ((447722236073/10000000000000 : ℚ) : ℝ) ≤ stT385o2 494 := by
  have hc : ((995113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((494 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((447722236073/10000000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((995113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c495 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((495 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((957993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62045577/20000000 : ℚ) : ℝ) ≤ Real.log ((495 : ℕ)) / 2 := by
    have h := (log_br_495).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((495 : ℕ)) / 2 ≤ ((31022789/10000000 : ℚ) : ℝ) := by
    have h := (log_br_495).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 363597/5000000) (δ := 2429/250000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t495 : ((215281404219/5000000000000 : ℚ) : ℝ) ≤ stT385o2 495 := by
  have hc : ((957943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((495 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215281404219/5000000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((957943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c496 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((496 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((388981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62065759/20000000 : ℚ) : ℝ) ≤ Real.log ((496 : ℕ)) / 2 := by
    have h := (log_br_496).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((496 : ℕ)) / 2 ≤ ((387911/125000 : ℚ) : ℝ) := by
    have h := (log_br_496).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1698453/10000000) (δ := 1227/125000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t496 : ((43661575107/1250000000000 : ℚ) : ℝ) ≤ stT385o2 496 := by
  have hc : ((97239/125000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((496 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43661575107/1250000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((97239/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c497 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((497 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((48267/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((620859/200000 : ℚ) : ℝ) ≤ Real.log ((497 : ℕ)) / 2 := by
    have h := (log_br_497).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((497 : ℕ)) / 2 ≤ ((62085901/20000000 : ℚ) : ℝ) := by
    have h := (log_br_497).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1333869/5000000) (δ := 9687/1000000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t497 : ((10824225491/500000000000 : ℚ) : ℝ) ≤ stT385o2 497 := by
  have hc : ((24131/50000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((497 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10824225491/500000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((24131/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c498 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((498 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((116511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((31053/10000 : ℚ) : ℝ) ≤ Real.log ((498 : ℕ)) / 2 := by
    have h := (log_br_498).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((498 : ℕ)) / 2 ≤ ((62106001/20000000 : ℚ) : ℝ) := by
    have h := (log_br_498).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3635051/10000000) (δ := 4883/500000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t498 : ((5218733871/1000000000000 : ℚ) : ℝ) ≤ stT385o2 498 := by
  have hc : ((116461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((498 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).1
  have hw2 : ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((44811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5218733871/1000000000000 : ℚ) : ℝ)
      = ((44811/1000000 : ℚ) : ℝ) * ((116461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c499 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((499 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-266133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3106303/1000000 : ℚ) : ℝ) ≤ Real.log ((499 : ℕ)) / 2 := by
    have h := (log_br_499).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((499 : ℕ)) / 2 ≤ ((62126061/20000000 : ℚ) : ℝ) := by
    have h := (log_br_499).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2300219/5000000) (δ := 9687/1000000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t499 : ((-59580007073/5000000000000 : ℚ) : ℝ) ≤ stT385o2 499 := by
  have hc : ((-266183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((499 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59580007073/5000000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-266183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_c500 :
    |Real.cos (((385 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((-152243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log ((500 : ℕ)) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((500 : ℕ)) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5563901/10000000) (δ := 4883/500000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st385o2_t500 : ((-68090791177/2500000000000 : ℚ) : ℝ) ≤ stT385o2 500 := by
  have hc : ((-304511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((385 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st385o2_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68090791177/2500000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-304511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st385o2_p1 : ((960651/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT385o2 (i+1) := by
  rw [Finset.sum_range_one]
  exact st385o2_t1

theorem st385o2_p2 : ((12150913251811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 1, stT385o2 (i+1)) + stT385o2 2 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 1
    simpa using h
  have hprev := st385o2_p1
  have hstep := st385o2_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p3 : ((121728068041/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 2, stT385o2 (i+1)) + stT385o2 3 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 2
    simpa using h
  have hprev := st385o2_p2
  have hstep := st385o2_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p4 : ((329902545631/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 3, stT385o2 (i+1)) + stT385o2 4 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 3
    simpa using h
  have hprev := st385o2_p3
  have hstep := st385o2_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p5 : ((1451437352579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 4, stT385o2 (i+1)) + stT385o2 5 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 4
    simpa using h
  have hprev := st385o2_p4
  have hstep := st385o2_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p6 : ((2650650110151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 5, stT385o2 (i+1)) + stT385o2 6 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 5
    simpa using h
  have hprev := st385o2_p5
  have hstep := st385o2_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p7 : ((954579772141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 6, stT385o2 (i+1)) + stT385o2 7 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 6
    simpa using h
  have hprev := st385o2_p6
  have hstep := st385o2_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p8 : ((21410177159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 7, stT385o2 (i+1)) + stT385o2 8 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 7
    simpa using h
  have hprev := st385o2_p7
  have hstep := st385o2_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p9 : ((-19021969229/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 8, stT385o2 (i+1)) + stT385o2 9 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 8
    simpa using h
  have hprev := st385o2_p8
  have hstep := st385o2_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p10 : ((-885717293481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 9, stT385o2 (i+1)) + stT385o2 10 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 9
    simpa using h
  have hprev := st385o2_p9
  have hstep := st385o2_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p11 : ((-3094106304039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 10, stT385o2 (i+1)) + stT385o2 11 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 10
    simpa using h
  have hprev := st385o2_p10
  have hstep := st385o2_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p12 : ((-3714096682769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 11, stT385o2 (i+1)) + stT385o2 12 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 11
    simpa using h
  have hprev := st385o2_p11
  have hstep := st385o2_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p13 : ((-3203651027659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 12, stT385o2 (i+1)) + stT385o2 13 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 12
    simpa using h
  have hprev := st385o2_p12
  have hstep := st385o2_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p14 : ((-2720432087611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 13, stT385o2 (i+1)) + stT385o2 14 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 13
    simpa using h
  have hprev := st385o2_p13
  have hstep := st385o2_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p15 : ((-315796333719/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 14, stT385o2 (i+1)) + stT385o2 15 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 14
    simpa using h
  have hprev := st385o2_p14
  have hstep := st385o2_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p16 : ((-113610333719/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 15, stT385o2 (i+1)) + stT385o2 16 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 15
    simpa using h
  have hprev := st385o2_p15
  have hstep := st385o2_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p17 : ((-512393386429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 16, stT385o2 (i+1)) + stT385o2 17 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 16
    simpa using h
  have hprev := st385o2_p16
  have hstep := st385o2_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p18 : ((-422321402907/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 17, stT385o2 (i+1)) + stT385o2 18 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 17
    simpa using h
  have hprev := st385o2_p17
  have hstep := st385o2_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p19 : ((-276312074799/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 18, stT385o2 (i+1)) + stT385o2 19 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 18
    simpa using h
  have hprev := st385o2_p18
  have hstep := st385o2_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p20 : ((-150038223243/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 19, stT385o2 (i+1)) + stT385o2 20 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 19
    simpa using h
  have hprev := st385o2_p19
  have hstep := st385o2_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p21 : ((-1072193388831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 20, stT385o2 (i+1)) + stT385o2 21 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 20
    simpa using h
  have hprev := st385o2_p20
  have hstep := st385o2_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p22 : ((-1663039963883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 21, stT385o2 (i+1)) + stT385o2 22 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 21
    simpa using h
  have hprev := st385o2_p21
  have hstep := st385o2_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p23 : ((-125495018059/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 22, stT385o2 (i+1)) + stT385o2 23 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 22
    simpa using h
  have hprev := st385o2_p22
  have hstep := st385o2_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p24 : ((-1075421564711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 23, stT385o2 (i+1)) + stT385o2 24 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 23
    simpa using h
  have hprev := st385o2_p23
  have hstep := st385o2_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p25 : ((-49304000327/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 24, stT385o2 (i+1)) + stT385o2 25 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 24
    simpa using h
  have hprev := st385o2_p24
  have hstep := st385o2_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p26 : ((-1821242790647/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 25, stT385o2 (i+1)) + stT385o2 26 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 25
    simpa using h
  have hprev := st385o2_p25
  have hstep := st385o2_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p27 : ((-948413720897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 26, stT385o2 (i+1)) + stT385o2 27 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 26
    simpa using h
  have hprev := st385o2_p26
  have hstep := st385o2_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p28 : ((-41187661399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 27, stT385o2 (i+1)) + stT385o2 28 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 27
    simpa using h
  have hprev := st385o2_p27
  have hstep := st385o2_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p29 : ((634895500747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 28, stT385o2 (i+1)) + stT385o2 29 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 28
    simpa using h
  have hprev := st385o2_p28
  have hstep := st385o2_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p30 : ((2259318888861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 29, stT385o2 (i+1)) + stT385o2 30 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 29
    simpa using h
  have hprev := st385o2_p29
  have hstep := st385o2_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p31 : ((79719542613/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 30, stT385o2 (i+1)) + stT385o2 31 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 30
    simpa using h
  have hprev := st385o2_p30
  have hstep := st385o2_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p32 : ((1087101095183/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 31, stT385o2 (i+1)) + stT385o2 32 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 31
    simpa using h
  have hprev := st385o2_p31
  have hstep := st385o2_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p33 : ((1469913404567/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 32, stT385o2 (i+1)) + stT385o2 33 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 32
    simpa using h
  have hprev := st385o2_p32
  have hstep := st385o2_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p34 : ((3796559570779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 33, stT385o2 (i+1)) + stT385o2 34 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 33
    simpa using h
  have hprev := st385o2_p33
  have hstep := st385o2_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p35 : ((883672775609/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 34, stT385o2 (i+1)) + stT385o2 35 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 34
    simpa using h
  have hprev := st385o2_p34
  have hstep := st385o2_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p36 : ((2195217769563/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 35, stT385o2 (i+1)) + stT385o2 36 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 35
    simpa using h
  have hprev := st385o2_p35
  have hstep := st385o2_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p37 : ((3680526955331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 36, stT385o2 (i+1)) + stT385o2 37 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 36
    simpa using h
  have hprev := st385o2_p36
  have hstep := st385o2_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p38 : ((3020866203301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 37, stT385o2 (i+1)) + stT385o2 38 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 37
    simpa using h
  have hprev := st385o2_p37
  have hstep := st385o2_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p39 : ((3282701267297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 38, stT385o2 (i+1)) + stT385o2 39 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 38
    simpa using h
  have hprev := st385o2_p38
  have hstep := st385o2_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p40 : ((50769692251/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 39, stT385o2 (i+1)) + stT385o2 40 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 39
    simpa using h
  have hprev := st385o2_p39
  have hstep := st385o2_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p41 : ((1979771175663/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 40, stT385o2 (i+1)) + stT385o2 41 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 40
    simpa using h
  have hprev := st385o2_p40
  have hstep := st385o2_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p42 : ((801019383507/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 41, stT385o2 (i+1)) + stT385o2 42 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 41
    simpa using h
  have hprev := st385o2_p41
  have hstep := st385o2_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p43 : ((3492066376323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 42, stT385o2 (i+1)) + stT385o2 43 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 42
    simpa using h
  have hprev := st385o2_p42
  have hstep := st385o2_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p44 : ((4080852171237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 43, stT385o2 (i+1)) + stT385o2 44 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 43
    simpa using h
  have hprev := st385o2_p43
  have hstep := st385o2_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p45 : ((3430365082917/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 44, stT385o2 (i+1)) + stT385o2 45 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 44
    simpa using h
  have hprev := st385o2_p44
  have hstep := st385o2_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p46 : ((3409171769837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 45, stT385o2 (i+1)) + stT385o2 46 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 45
    simpa using h
  have hprev := st385o2_p45
  have hstep := st385o2_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p47 : ((2016641229409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 46, stT385o2 (i+1)) + stT385o2 47 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 46
    simpa using h
  have hprev := st385o2_p46
  have hstep := st385o2_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p48 : ((1679868410961/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 47, stT385o2 (i+1)) + stT385o2 48 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 47
    simpa using h
  have hprev := st385o2_p47
  have hstep := st385o2_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p49 : ((3621809600443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 48, stT385o2 (i+1)) + stT385o2 49 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 48
    simpa using h
  have hprev := st385o2_p48
  have hstep := st385o2_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p50 : ((3878605225409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 49, stT385o2 (i+1)) + stT385o2 50 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 49
    simpa using h
  have hprev := st385o2_p49
  have hstep := st385o2_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p51 : ((6548029999731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 50, stT385o2 (i+1)) + stT385o2 51 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 50
    simpa using h
  have hprev := st385o2_p50
  have hstep := st385o2_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p52 : ((7931532231231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 51, stT385o2 (i+1)) + stT385o2 52 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 51
    simpa using h
  have hprev := st385o2_p51
  have hstep := st385o2_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p53 : ((1358460649881/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 52, stT385o2 (i+1)) + stT385o2 53 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 52
    simpa using h
  have hprev := st385o2_p52
  have hstep := st385o2_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p54 : ((3734942434209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 53, stT385o2 (i+1)) + stT385o2 54 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 53
    simpa using h
  have hprev := st385o2_p53
  have hstep := st385o2_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p55 : ((3647077319209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 54, stT385o2 (i+1)) + stT385o2 55 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 54
    simpa using h
  have hprev := st385o2_p54
  have hstep := st385o2_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p56 : ((351671121721/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 55, stT385o2 (i+1)) + stT385o2 56 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 55
    simpa using h
  have hprev := st385o2_p55
  have hstep := st385o2_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p57 : ((1905909135671/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 56, stT385o2 (i+1)) + stT385o2 57 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 56
    simpa using h
  have hprev := st385o2_p56
  have hstep := st385o2_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p58 : ((6809997128499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 57, stT385o2 (i+1)) + stT385o2 58 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 57
    simpa using h
  have hprev := st385o2_p57
  have hstep := st385o2_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p59 : ((6207529119/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 58, stT385o2 (i+1)) + stT385o2 59 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 58
    simpa using h
  have hprev := st385o2_p58
  have hstep := st385o2_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p60 : ((1347848524169/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 59, stT385o2 (i+1)) + stT385o2 60 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 59
    simpa using h
  have hprev := st385o2_p59
  have hstep := st385o2_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p61 : ((7781678555037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 60, stT385o2 (i+1)) + stT385o2 61 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 60
    simpa using h
  have hprev := st385o2_p60
  have hstep := st385o2_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p62 : ((1351212353979/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 61, stT385o2 (i+1)) + stT385o2 62 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 61
    simpa using h
  have hprev := st385o2_p61
  have hstep := st385o2_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p63 : ((7725769497737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 62, stT385o2 (i+1)) + stT385o2 63 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 62
    simpa using h
  have hprev := st385o2_p62
  have hstep := st385o2_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p64 : ((6856996302719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 63, stT385o2 (i+1)) + stT385o2 64 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 63
    simpa using h
  have hprev := st385o2_p63
  have hstep := st385o2_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p65 : ((3784426265959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 64, stT385o2 (i+1)) + stT385o2 65 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 64
    simpa using h
  have hprev := st385o2_p64
  have hstep := st385o2_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p66 : ((884944554241/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 65, stT385o2 (i+1)) + stT385o2 66 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 65
    simpa using h
  have hprev := st385o2_p65
  have hstep := st385o2_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p67 : ((3638240034047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 66, stT385o2 (i+1)) + stT385o2 67 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 66
    simpa using h
  have hprev := st385o2_p66
  have hstep := st385o2_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p68 : ((928863265331/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 67, stT385o2 (i+1)) + stT385o2 68 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 67
    simpa using h
  have hprev := st385o2_p67
  have hstep := st385o2_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p69 : ((6897405172067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 68, stT385o2 (i+1)) + stT385o2 69 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 68
    simpa using h
  have hprev := st385o2_p68
  have hstep := st385o2_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p70 : ((7780011726843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 69, stT385o2 (i+1)) + stT385o2 70 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 69
    simpa using h
  have hprev := st385o2_p69
  have hstep := st385o2_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p71 : ((6656786650071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 70, stT385o2 (i+1)) + stT385o2 71 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 70
    simpa using h
  have hprev := st385o2_p70
  have hstep := st385o2_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p72 : ((7826718089991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 71, stT385o2 (i+1)) + stT385o2 72 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 71
    simpa using h
  have hprev := st385o2_p71
  have hstep := st385o2_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p73 : ((6865129828619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 72, stT385o2 (i+1)) + stT385o2 73 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 72
    simpa using h
  have hprev := st385o2_p72
  have hstep := st385o2_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p74 : ((7361873260559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 73, stT385o2 (i+1)) + stT385o2 74 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 73
    simpa using h
  have hprev := st385o2_p73
  have hstep := st385o2_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p75 : ((7495540177859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 74, stT385o2 (i+1)) + stT385o2 75 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 74
    simpa using h
  have hprev := st385o2_p74
  have hstep := st385o2_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p76 : ((1349910681863/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 75, stT385o2 (i+1)) + stT385o2 76 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 75
    simpa using h
  have hprev := st385o2_p75
  have hstep := st385o2_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p77 : ((1571415705713/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 76, stT385o2 (i+1)) + stT385o2 77 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 76
    simpa using h
  have hprev := st385o2_p76
  have hstep := st385o2_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p78 : ((6823181899429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 77, stT385o2 (i+1)) + stT385o2 78 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 77
    simpa using h
  have hprev := st385o2_p77
  have hstep := st385o2_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p79 : ((1464802425461/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 78, stT385o2 (i+1)) + stT385o2 79 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 78
    simpa using h
  have hprev := st385o2_p78
  have hstep := st385o2_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p80 : ((1522012174071/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 79, stT385o2 (i+1)) + stT385o2 80 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 79
    simpa using h
  have hprev := st385o2_p79
  have hstep := st385o2_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p81 : ((6669647895803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 80, stT385o2 (i+1)) + stT385o2 81 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 80
    simpa using h
  have hprev := st385o2_p80
  have hstep := st385o2_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p82 : ((7747808299343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 81, stT385o2 (i+1)) + stT385o2 82 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 81
    simpa using h
  have hprev := st385o2_p81
  have hstep := st385o2_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p83 : ((7178967986309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 82, stT385o2 (i+1)) + stT385o2 83 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 82
    simpa using h
  have hprev := st385o2_p82
  have hstep := st385o2_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p84 : ((6865395266849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 83, stT385o2 (i+1)) + stT385o2 84 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 83
    simpa using h
  have hprev := st385o2_p83
  have hstep := st385o2_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p85 : ((7857537297769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 84, stT385o2 (i+1)) + stT385o2 85 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 84
    simpa using h
  have hprev := st385o2_p84
  have hstep := st385o2_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p86 : ((6898154267809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 85, stT385o2 (i+1)) + stT385o2 86 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 85
    simpa using h
  have hprev := st385o2_p85
  have hstep := st385o2_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p87 : ((7090511530737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 86, stT385o2 (i+1)) + stT385o2 87 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 86
    simpa using h
  have hprev := st385o2_p86
  have hstep := st385o2_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p88 : ((3912857838893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 87, stT385o2 (i+1)) + stT385o2 88 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 87
    simpa using h
  have hprev := st385o2_p87
  have hstep := st385o2_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p89 : ((3389331186681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 88, stT385o2 (i+1)) + stT385o2 89 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 88
    simpa using h
  have hprev := st385o2_p88
  have hstep := st385o2_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p90 : ((3605800573893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 89, stT385o2 (i+1)) + stT385o2 90 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 89
    simpa using h
  have hprev := st385o2_p89
  have hstep := st385o2_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p91 : ((3897907007061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 90, stT385o2 (i+1)) + stT385o2 91 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 90
    simpa using h
  have hprev := st385o2_p90
  have hstep := st385o2_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p92 : ((3377475416921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 91, stT385o2 (i+1)) + stT385o2 92 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 91
    simpa using h
  have hprev := st385o2_p91
  have hstep := st385o2_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p93 : ((3603972476047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 92, stT385o2 (i+1)) + stT385o2 93 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 92
    simpa using h
  have hprev := st385o2_p92
  have hstep := st385o2_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p94 : ((781604601959/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 93, stT385o2 (i+1)) + stT385o2 94 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 93
    simpa using h
  have hprev := st385o2_p93
  have hstep := st385o2_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p95 : ((6803838735707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 94, stT385o2 (i+1)) + stT385o2 95 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 94
    simpa using h
  have hprev := st385o2_p94
  have hstep := st385o2_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p96 : ((7086421877587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 95, stT385o2 (i+1)) + stT385o2 96 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 95
    simpa using h
  have hprev := st385o2_p95
  have hstep := st385o2_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p97 : ((7859911445041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 96, stT385o2 (i+1)) + stT385o2 97 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 96
    simpa using h
  have hprev := st385o2_p96
  have hstep := st385o2_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p98 : ((217370999601/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 97, stT385o2 (i+1)) + stT385o2 98 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 97
    simpa using h
  have hprev := st385o2_p97
  have hstep := st385o2_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p99 : ((687646493989/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 98, stT385o2 (i+1)) + stT385o2 99 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 98
    simpa using h
  have hprev := st385o2_p98
  have hstep := st385o2_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p100 : ((1567223796047/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 99, stT385o2 (i+1)) + stT385o2 100 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 99
    simpa using h
  have hprev := st385o2_p99
  have hstep := st385o2_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p101 : ((7250249561177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 100, stT385o2 (i+1)) + stT385o2 101 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 100
    simpa using h
  have hprev := st385o2_p100
  have hstep := st385o2_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p102 : ((6678501470501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 101, stT385o2 (i+1)) + stT385o2 102 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 101
    simpa using h
  have hprev := st385o2_p101
  have hstep := st385o2_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p103 : ((3808665904831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 102, stT385o2 (i+1)) + stT385o2 103 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 102
    simpa using h
  have hprev := st385o2_p102
  have hstep := st385o2_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p104 : ((3818030934121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 103, stT385o2 (i+1)) + stT385o2 104 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 103
    simpa using h
  have hprev := st385o2_p103
  have hstep := st385o2_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p105 : ((6690978845921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 104, stT385o2 (i+1)) + stT385o2 105 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 104
    simpa using h
  have hprev := st385o2_p104
  have hstep := st385o2_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p106 : ((7161723776591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 105, stT385o2 (i+1)) + stT385o2 106 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 105
    simpa using h
  have hprev := st385o2_p105
  have hstep := st385o2_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p107 : ((7873769310447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 106, stT385o2 (i+1)) + stT385o2 107 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 106
    simpa using h
  have hprev := st385o2_p106
  have hstep := st385o2_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p108 : ((110687062069/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 107, stT385o2 (i+1)) + stT385o2 108 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 107
    simpa using h
  have hprev := st385o2_p107
  have hstep := st385o2_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p109 : ((838347462477/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 108, stT385o2 (i+1)) + stT385o2 109 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 108
    simpa using h
  have hprev := st385o2_p108
  have hstep := st385o2_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p110 : ((1909432615499/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 109, stT385o2 (i+1)) + stT385o2 110 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 109
    simpa using h
  have hprev := st385o2_p109
  have hstep := st385o2_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p111 : ((153630149623/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 110, stT385o2 (i+1)) + stT385o2 111 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 110
    simpa using h
  have hprev := st385o2_p110
  have hstep := st385o2_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p112 : ((3371102239391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 111, stT385o2 (i+1)) + stT385o2 112 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 111
    simpa using h
  have hprev := st385o2_p111
  have hstep := st385o2_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p113 : ((3487359709511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 112, stT385o2 (i+1)) + stT385o2 113 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 112
    simpa using h
  have hprev := st385o2_p112
  have hstep := st385o2_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p114 : ((7846154629837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 113, stT385o2 (i+1)) + stT385o2 114 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 113
    simpa using h
  have hprev := st385o2_p113
  have hstep := st385o2_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p115 : ((7410960141367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 114, stT385o2 (i+1)) + stT385o2 115 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 114
    simpa using h
  have hprev := st385o2_p114
  have hstep := st385o2_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p116 : ((1326994126597/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 115, stT385o2 (i+1)) + stT385o2 116 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 115
    simpa using h
  have hprev := st385o2_p115
  have hstep := st385o2_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p117 : ((1440779922497/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 116, stT385o2 (i+1)) + stT385o2 117 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 116
    simpa using h
  have hprev := st385o2_p116
  have hstep := st385o2_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p118 : ((7889559698017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 117, stT385o2 (i+1)) + stT385o2 118 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 117
    simpa using h
  have hprev := st385o2_p117
  have hstep := st385o2_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p119 : ((3621065472789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 118, stT385o2 (i+1)) + stT385o2 119 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 118
    simpa using h
  have hprev := st385o2_p118
  have hstep := st385o2_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p120 : ((1655534087127/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 119, stT385o2 (i+1)) + stT385o2 120 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 119
    simpa using h
  have hprev := st385o2_p119
  have hstep := st385o2_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p121 : ((3652822832499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 120, stT385o2 (i+1)) + stT385o2 121 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 120
    simpa using h
  have hprev := st385o2_p120
  have hstep := st385o2_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p122 : ((7893174374077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 121, stT385o2 (i+1)) + stT385o2 122 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 121
    simpa using h
  have hprev := st385o2_p121
  have hstep := st385o2_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p123 : ((7206772676557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 122, stT385o2 (i+1)) + stT385o2 123 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 122
    simpa using h
  have hprev := st385o2_p122
  have hstep := st385o2_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p124 : ((3308064322153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 123, stT385o2 (i+1)) + stT385o2 124 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 123
    simpa using h
  have hprev := st385o2_p123
  have hstep := st385o2_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p125 : ((7275195229099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 124, stT385o2 (i+1)) + stT385o2 125 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 124
    simpa using h
  have hprev := st385o2_p124
  have hstep := st385o2_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p126 : ((7901191760699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 125, stT385o2 (i+1)) + stT385o2 126 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 125
    simpa using h
  have hprev := st385o2_p125
  have hstep := st385o2_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p127 : ((3650587133827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 126, stT385o2 (i+1)) + stT385o2 127 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 126
    simpa using h
  have hprev := st385o2_p126
  have hstep := st385o2_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p128 : ((3307346692339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 127, stT385o2 (i+1)) + stT385o2 128 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 127
    simpa using h
  have hprev := st385o2_p127
  have hstep := st385o2_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p129 : ((3559082314989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 128, stT385o2 (i+1)) + stT385o2 129 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 128
    simpa using h
  have hprev := st385o2_p128
  have hstep := st385o2_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p130 : ((393864188183/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 129, stT385o2 (i+1)) + stT385o2 130 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 129
    simpa using h
  have hprev := st385o2_p129
  have hstep := st385o2_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p131 : ((1502794027961/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 130, stT385o2 (i+1)) + stT385o2 131 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 130
    simpa using h
  have hprev := st385o2_p130
  have hstep := st385o2_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p132 : ((836030208723/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 131, stT385o2 (i+1)) + stT385o2 132 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 131
    simpa using h
  have hprev := st385o2_p131
  have hstep := st385o2_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p133 : ((3431902614507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 132, stT385o2 (i+1)) + stT385o2 133 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 132
    simpa using h
  have hprev := st385o2_p132
  have hstep := st385o2_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p134 : ((772519565559/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 133, stT385o2 (i+1)) + stT385o2 134 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 133
    simpa using h
  have hprev := st385o2_p133
  have hstep := st385o2_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p135 : ((1945153205277/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 134, stT385o2 (i+1)) + stT385o2 135 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 134
    simpa using h
  have hprev := st385o2_p134
  have hstep := st385o2_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p136 : ((6942748693371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 135, stT385o2 (i+1)) + stT385o2 136 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 135
    simpa using h
  have hprev := st385o2_p135
  have hstep := st385o2_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p137 : ((1325934353469/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 136, stT385o2 (i+1)) + stT385o2 137 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 136
    simpa using h
  have hprev := st385o2_p136
  have hstep := st385o2_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p138 : ((7357148334897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 137, stT385o2 (i+1)) + stT385o2 138 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 137
    simpa using h
  have hprev := st385o2_p137
  have hstep := st385o2_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p139 : ((7920726003309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 138, stT385o2 (i+1)) + stT385o2 139 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 138
    simpa using h
  have hprev := st385o2_p138
  have hstep := st385o2_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p140 : ((7407115167949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 139, stT385o2 (i+1)) + stT385o2 140 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 139
    simpa using h
  have hprev := st385o2_p139
  have hstep := st385o2_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p141 : ((6649647446613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 140, stT385o2 (i+1)) + stT385o2 141 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 140
    simpa using h
  have hprev := st385o2_p140
  have hstep := st385o2_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p142 : ((3425378167041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 141, stT385o2 (i+1)) + stT385o2 142 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 141
    simpa using h
  have hprev := st385o2_p141
  have hstep := st385o2_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p143 : ((1921687910673/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 142, stT385o2 (i+1)) + stT385o2 143 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 142
    simpa using h
  have hprev := st385o2_p142
  have hstep := st385o2_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p144 : ((1964534560201/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 143, stT385o2 (i+1)) + stT385o2 144 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 143
    simpa using h
  have hprev := st385o2_p143
  have hstep := st385o2_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p145 : ((7108802915659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 144, stT385o2 (i+1)) + stT385o2 145 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 144
    simpa using h
  have hprev := st385o2_p144
  have hstep := st385o2_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p146 : ((6579692882103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 145, stT385o2 (i+1)) + stT385o2 146 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 145
    simpa using h
  have hprev := st385o2_p145
  have hstep := st385o2_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p147 : ((7059169026627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 146, stT385o2 (i+1)) + stT385o2 147 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 146
    simpa using h
  have hprev := st385o2_p146
  have hstep := st385o2_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p148 : ((313197848979/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 147, stT385o2 (i+1)) + stT385o2 148 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 147
    simpa using h
  have hprev := st385o2_p147
  have hstep := st385o2_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p149 : ((7764238083451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 148, stT385o2 (i+1)) + stT385o2 149 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 148
    simpa using h
  have hprev := st385o2_p148
  have hstep := st385o2_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p150 : ((1392891282007/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 149, stT385o2 (i+1)) + stT385o2 150 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 149
    simpa using h
  have hprev := st385o2_p149
  have hstep := st385o2_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p151 : ((6578090551349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 150, stT385o2 (i+1)) + stT385o2 151 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 150
    simpa using h
  have hprev := st385o2_p150
  have hstep := st385o2_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p152 : ((893270593729/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 151, stT385o2 (i+1)) + stT385o2 152 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 151
    simpa using h
  have hprev := st385o2_p151
  have hstep := st385o2_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p153 : ((1966957963247/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 152, stT385o2 (i+1)) + stT385o2 153 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 152
    simpa using h
  have hprev := st385o2_p152
  have hstep := st385o2_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p154 : ((3873378473619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 153, stT385o2 (i+1)) + stT385o2 154 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 153
    simpa using h
  have hprev := st385o2_p153
  have hstep := st385o2_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p155 : ((3477817523439/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 154, stT385o2 (i+1)) + stT385o2 155 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 154
    simpa using h
  have hprev := st385o2_p154
  have hstep := st385o2_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p156 : ((6566895818943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 155, stT385o2 (i+1)) + stT385o2 156 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 155
    simpa using h
  have hprev := st385o2_p155
  have hstep := st385o2_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p157 : ((7094970171079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 156, stT385o2 (i+1)) + stT385o2 157 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 156
    simpa using h
  have hprev := st385o2_p156
  have hstep := st385o2_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p158 : ((1958833851051/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 157, stT385o2 (i+1)) + stT385o2 158 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 157
    simpa using h
  have hprev := st385o2_p157
  have hstep := st385o2_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p159 : ((12220014173/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 158, stT385o2 (i+1)) + stT385o2 159 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 158
    simpa using h
  have hprev := st385o2_p158
  have hstep := st385o2_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p160 : ((44230951693/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 159, stT385o2 (i+1)) + stT385o2 160 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 159
    simpa using h
  have hprev := st385o2_p159
  have hstep := st385o2_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p161 : ((3279495767841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 160, stT385o2 (i+1)) + stT385o2 161 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 160
    simpa using h
  have hprev := st385o2_p160
  have hstep := st385o2_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p162 : ((3459102415589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 161, stT385o2 (i+1)) + stT385o2 162 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 161
    simpa using h
  have hprev := st385o2_p161
  have hstep := st385o2_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p163 : ((3849172161669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 162, stT385o2 (i+1)) + stT385o2 163 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 162
    simpa using h
  have hprev := st385o2_p162
  have hstep := st385o2_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p164 : ((3966283230403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 163, stT385o2 (i+1)) + stT385o2 164 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 163
    simpa using h
  have hprev := st385o2_p163
  have hstep := st385o2_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p165 : ((1467951164157/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 164, stT385o2 (i+1)) + stT385o2 165 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 164
    simpa using h
  have hprev := st385o2_p164
  have hstep := st385o2_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p166 : ((1328701913247/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 165, stT385o2 (i+1)) + stT385o2 166 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 165
    simpa using h
  have hprev := st385o2_p165
  have hstep := st385o2_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p167 : ((333845968713/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 166, stT385o2 (i+1)) + stT385o2 167 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 166
    simpa using h
  have hprev := st385o2_p166
  have hstep := st385o2_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p168 : ((924230266323/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 167, stT385o2 (i+1)) + stT385o2 168 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 167
    simpa using h
  have hprev := st385o2_p167
  have hstep := st385o2_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p169 : ((3974586556857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 168, stT385o2 (i+1)) + stT385o2 169 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 168
    simpa using h
  have hprev := st385o2_p168
  have hstep := st385o2_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p170 : ((3850654216437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 169, stT385o2 (i+1)) + stT385o2 170 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 169
    simpa using h
  have hprev := st385o2_p169
  have hstep := st385o2_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p171 : ((3470702319717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 170, stT385o2 (i+1)) + stT385o2 171 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 170
    simpa using h
  have hprev := st385o2_p170
  have hstep := st385o2_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p172 : ((3267821232249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 171, stT385o2 (i+1)) + stT385o2 172 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 171
    simpa using h
  have hprev := st385o2_p171
  have hstep := st385o2_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p173 : ((6936141595373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 172, stT385o2 (i+1)) + stT385o2 173 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 172
    simpa using h
  have hprev := st385o2_p172
  have hstep := st385o2_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p174 : ((7690885011723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 173, stT385o2 (i+1)) + stT385o2 174 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 173
    simpa using h
  have hprev := st385o2_p173
  have hstep := st385o2_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p175 : ((7967061794667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 174, stT385o2 (i+1)) + stT385o2 175 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 174
    simpa using h
  have hprev := st385o2_p174
  have hstep := st385o2_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p176 : ((7468406835007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 175, stT385o2 (i+1)) + stT385o2 176 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 175
    simpa using h
  have hprev := st385o2_p175
  have hstep := st385o2_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p177 : ((1684686565351/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 176, stT385o2 (i+1)) + stT385o2 177 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 176
    simpa using h
  have hprev := st385o2_p176
  have hstep := st385o2_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p178 : ((819738990311/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 177, stT385o2 (i+1)) + stT385o2 178 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 177
    simpa using h
  have hprev := st385o2_p177
  have hstep := st385o2_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p179 : ((7111859171473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 178, stT385o2 (i+1)) + stT385o2 179 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 178
    simpa using h
  have hprev := st385o2_p178
  have hstep := st385o2_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p180 : ((3907693542469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 179, stT385o2 (i+1)) + stT385o2 180 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 179
    simpa using h
  have hprev := st385o2_p179
  have hstep := st385o2_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p181 : ((3969766767703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 180, stT385o2 (i+1)) + stT385o2 181 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 180
    simpa using h
  have hprev := st385o2_p180
  have hstep := st385o2_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p182 : ((920277020207/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 181, stT385o2 (i+1)) + stT385o2 182 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 181
    simpa using h
  have hprev := st385o2_p181
  have hstep := st385o2_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p183 : ((3337400528541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 182, stT385o2 (i+1)) + stT385o2 183 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 182
    simpa using h
  have hprev := st385o2_p182
  have hstep := st385o2_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p184 : ((3284120887421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 183, stT385o2 (i+1)) + stT385o2 184 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 183
    simpa using h
  have hprev := st385o2_p183
  have hstep := st385o2_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p185 : ((111615172089/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 184, stT385o2 (i+1)) + stT385o2 185 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 184
    simpa using h
  have hprev := st385o2_p184
  have hstep := st385o2_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p186 : ((7828188306941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 185, stT385o2 (i+1)) + stT385o2 186 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 185
    simpa using h
  have hprev := st385o2_p185
  have hstep := st385o2_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p187 : ((7954255943381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 186, stT385o2 (i+1)) + stT385o2 187 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 186
    simpa using h
  have hprev := st385o2_p186
  have hstep := st385o2_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p188 : ((7404683300181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 187, stT385o2 (i+1)) + stT385o2 188 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 187
    simpa using h
  have hprev := st385o2_p187
  have hstep := st385o2_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p189 : ((209705016519/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 188, stT385o2 (i+1)) + stT385o2 189 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 188
    simpa using h
  have hprev := st385o2_p188
  have hstep := st385o2_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p190 : ((3265101296773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 189, stT385o2 (i+1)) + stT385o2 190 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 189
    simpa using h
  have hprev := st385o2_p189
  have hstep := st385o2_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p191 : ((3514147508259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 190, stT385o2 (i+1)) + stT385o2 191 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 190
    simpa using h
  have hprev := st385o2_p190
  have hstep := st385o2_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p192 : ((1547288778017/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 191, stT385o2 (i+1)) + stT385o2 192 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 191
    simpa using h
  have hprev := st385o2_p191
  have hstep := st385o2_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p193 : ((400071721237/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 192, stT385o2 (i+1)) + stT385o2 193 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 192
    simpa using h
  have hprev := st385o2_p192
  have hstep := st385o2_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p194 : ((7585535853179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 193, stT385o2 (i+1)) + stT385o2 194 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 193
    simpa using h
  have hprev := st385o2_p193
  have hstep := st385o2_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p195 : ((6869867708939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 194, stT385o2 (i+1)) + stT385o2 195 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 194
    simpa using h
  have hprev := st385o2_p194
  have hstep := st385o2_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p196 : ((6496828274009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 195, stT385o2 (i+1)) + stT385o2 196 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 195
    simpa using h
  have hprev := st385o2_p195
  have hstep := st385o2_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p197 : ((6793941800939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 196, stT385o2 (i+1)) + stT385o2 197 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 196
    simpa using h
  have hprev := st385o2_p196
  have hstep := st385o2_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p198 : ((1873704623197/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 197, stT385o2 (i+1)) + stT385o2 198 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 197
    simpa using h
  have hprev := st385o2_p197
  have hstep := st385o2_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p199 : ((3993343458367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 198, stT385o2 (i+1)) + stT385o2 199 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 198
    simpa using h
  have hprev := st385o2_p198
  have hstep := st385o2_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p200 : ((784756220027/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 199, stT385o2 (i+1)) + stT385o2 200 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 199
    simpa using h
  have hprev := st385o2_p199
  have hstep := st385o2_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p201 : ((18003495641/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 200, stT385o2 (i+1)) + stT385o2 201 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 200
    simpa using h
  have hprev := st385o2_p200
  have hstep := st385o2_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p202 : ((824854264351/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 201, stT385o2 (i+1)) + stT385o2 202 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 201
    simpa using h
  have hprev := st385o2_p201
  have hstep := st385o2_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p203 : ((6544427800637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 202, stT385o2 (i+1)) + stT385o2 203 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 202
    simpa using h
  have hprev := st385o2_p202
  have hstep := st385o2_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p204 : ((7078807555217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 203, stT385o2 (i+1)) + stT385o2 204 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 203
    simpa using h
  have hprev := st385o2_p203
  have hstep := st385o2_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p205 : ((7757361634277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 204, stT385o2 (i+1)) + stT385o2 205 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 204
    simpa using h
  have hprev := st385o2_p204
  have hstep := st385o2_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p206 : ((8025514657453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 205, stT385o2 (i+1)) + stT385o2 206 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 205
    simpa using h
  have hprev := st385o2_p205
  have hstep := st385o2_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p207 : ((191746851757/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 206, stT385o2 (i+1)) + stT385o2 207 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 206
    simpa using h
  have hprev := st385o2_p206
  have hstep := st385o2_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p208 : ((872544415121/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 207, stT385o2 (i+1)) + stT385o2 208 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 207
    simpa using h
  have hprev := st385o2_p207
  have hstep := st385o2_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p209 : ((6507036189633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 208, stT385o2 (i+1)) + stT385o2 209 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 208
    simpa using h
  have hprev := st385o2_p208
  have hstep := st385o2_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p210 : ((6620569823823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 209, stT385o2 (i+1)) + stT385o2 210 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 209
    simpa using h
  have hprev := st385o2_p209
  have hstep := st385o2_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p211 : ((7227640779639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 210, stT385o2 (i+1)) + stT385o2 211 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 210
    simpa using h
  have hprev := st385o2_p210
  have hstep := st385o2_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p212 : ((7854946495983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 211, stT385o2 (i+1)) + stT385o2 212 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 211
    simpa using h
  have hprev := st385o2_p211
  have hstep := st385o2_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p213 : ((8021593125027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 212, stT385o2 (i+1)) + stT385o2 213 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 212
    simpa using h
  have hprev := st385o2_p212
  have hstep := st385o2_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p214 : ((7604646680187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 213, stT385o2 (i+1)) + stT385o2 214 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 213
    simpa using h
  have hprev := st385o2_p213
  have hstep := st385o2_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p215 : ((6922721243677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 214, stT385o2 (i+1)) + stT385o2 215 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 214
    simpa using h
  have hprev := st385o2_p214
  have hstep := st385o2_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p216 : ((6486981396421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 215, stT385o2 (i+1)) + stT385o2 216 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 215
    simpa using h
  have hprev := st385o2_p215
  have hstep := st385o2_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p217 : ((6617938550149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 216, stT385o2 (i+1)) + stT385o2 217 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 216
    simpa using h
  have hprev := st385o2_p216
  have hstep := st385o2_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p218 : ((7214997787329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 217, stT385o2 (i+1)) + stT385o2 218 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 217
    simpa using h
  have hprev := st385o2_p217
  have hstep := st385o2_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p219 : ((7840099110971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 218, stT385o2 (i+1)) + stT385o2 219 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 218
    simpa using h
  have hprev := st385o2_p218
  have hstep := st385o2_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p220 : ((2010526159487/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 219, stT385o2 (i+1)) + stT385o2 220 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 219
    simpa using h
  have hprev := st385o2_p219
  have hstep := st385o2_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p221 : ((7679825158357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 220, stT385o2 (i+1)) + stT385o2 221 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 220
    simpa using h
  have hprev := st385o2_p220
  have hstep := st385o2_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p222 : ((701456695723/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 221, stT385o2 (i+1)) + stT385o2 222 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 221
    simpa using h
  have hprev := st385o2_p221
  have hstep := st385o2_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p223 : ((651647191213/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 222, stT385o2 (i+1)) + stT385o2 223 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 222
    simpa using h
  have hprev := st385o2_p222
  have hstep := st385o2_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p224 : ((6531550120881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 223, stT385o2 (i+1)) + stT385o2 224 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 223
    simpa using h
  have hprev := st385o2_p223
  have hstep := st385o2_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p225 : ((7045380940383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 224, stT385o2 (i+1)) + stT385o2 225 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 224
    simpa using h
  have hprev := st385o2_p224
  have hstep := st385o2_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p226 : ((7701726574143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 225, stT385o2 (i+1)) + stT385o2 226 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 225
    simpa using h
  have hprev := st385o2_p225
  have hstep := st385o2_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p227 : ((4026551097033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 226, stT385o2 (i+1)) + stT385o2 227 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 226
    simpa using h
  have hprev := st385o2_p226
  have hstep := st385o2_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p228 : ((3932417790187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 227, stT385o2 (i+1)) + stT385o2 228 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 227
    simpa using h
  have hprev := st385o2_p227
  have hstep := st385o2_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p229 : ((1816741219169/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 228, stT385o2 (i+1)) + stT385o2 229 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 228
    simpa using h
  have hprev := st385o2_p228
  have hstep := st385o2_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p230 : ((1664813242959/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 229, stT385o2 (i+1)) + stT385o2 230 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 229
    simpa using h
  have hprev := st385o2_p229
  have hstep := st385o2_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p231 : ((1610413607111/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 230, stT385o2 (i+1)) + stT385o2 231 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 230
    simpa using h
  have hprev := st385o2_p230
  have hstep := st385o2_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p232 : ((105518922383/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 231, stT385o2 (i+1)) + stT385o2 232 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 231
    simpa using h
  have hprev := st385o2_p231
  have hstep := st385o2_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p233 : ((7388203439787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 232, stT385o2 (i+1)) + stT385o2 233 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 232
    simpa using h
  have hprev := st385o2_p232
  have hstep := st385o2_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p234 : ((7936378384627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 233, stT385o2 (i+1)) + stT385o2 234 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 233
    simpa using h
  have hprev := st385o2_p233
  have hstep := st385o2_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p235 : ((1609830700319/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 234, stT385o2 (i+1)) + stT385o2 235 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 234
    simpa using h
  have hprev := st385o2_p234
  have hstep := st385o2_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p236 : ((382924931201/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 235, stT385o2 (i+1)) + stT385o2 236 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 235
    simpa using h
  have hprev := st385o2_p235
  have hstep := st385o2_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p237 : ((701305664137/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 236, stT385o2 (i+1)) + stT385o2 237 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 236
    simpa using h
  have hprev := st385o2_p236
  have hstep := st385o2_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p238 : ((3258058439303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 237, stT385o2 (i+1)) + stT385o2 238 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 237
    simpa using h
  have hprev := st385o2_p237
  have hstep := st385o2_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p239 : ((3236588293679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 238, stT385o2 (i+1)) + stT385o2 239 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 238
    simpa using h
  have hprev := st385o2_p238
  have hstep := st385o2_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p240 : ((1726786377863/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 239, stT385o2 (i+1)) + stT385o2 240 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 239
    simpa using h
  have hprev := st385o2_p239
  have hstep := st385o2_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p241 : ((1887729720697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 240, stT385o2 (i+1)) + stT385o2 241 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 240
    simpa using h
  have hprev := st385o2_p240
  have hstep := st385o2_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p242 : ((2003751738809/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 241, stT385o2 (i+1)) + stT385o2 242 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 241
    simpa using h
  have hprev := st385o2_p241
  have hstep := st385o2_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p243 : ((2005809350059/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 242, stT385o2 (i+1)) + stT385o2 243 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 242
    simpa using h
  have hprev := st385o2_p242
  have hstep := st385o2_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p244 : ((3787016834903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 243, stT385o2 (i+1)) + stT385o2 244 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 243
    simpa using h
  have hprev := st385o2_p243
  have hstep := st385o2_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p245 : ((1387027117373/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 244, stT385o2 (i+1)) + stT385o2 245 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 244
    simpa using h
  have hprev := st385o2_p244
  have hstep := st385o2_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p246 : ((32405441571/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 245, stT385o2 (i+1)) + stT385o2 246 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 245
    simpa using h
  have hprev := st385o2_p245
  have hstep := st385o2_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p247 : ((647371122591/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 246, stT385o2 (i+1)) + stT385o2 247 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 246
    simpa using h
  have hprev := st385o2_p246
  have hstep := st385o2_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p248 : ((691400498591/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 247, stT385o2 (i+1)) + stT385o2 248 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 247
    simpa using h
  have hprev := st385o2_p247
  have hstep := st385o2_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p249 : ((3773706695679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 248, stT385o2 (i+1)) + stT385o2 249 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 248
    simpa using h
  have hprev := st385o2_p248
  have hstep := st385o2_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p250 : ((8013731949683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 249, stT385o2 (i+1)) + stT385o2 250 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 249
    simpa using h
  have hprev := st385o2_p249
  have hstep := st385o2_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p251 : ((8051991142799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 250, stT385o2 (i+1)) + stT385o2 251 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 250
    simpa using h
  have hprev := st385o2_p250
  have hstep := st385o2_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p252 : ((1528776269237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 251, stT385o2 (i+1)) + stT385o2 252 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 251
    simpa using h
  have hprev := st385o2_p251
  have hstep := st385o2_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p253 : ((1403706703673/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 252, stT385o2 (i+1)) + stT385o2 253 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 252
    simpa using h
  have hprev := st385o2_p252
  have hstep := st385o2_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p254 : ((1304229829433/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 253, stT385o2 (i+1)) + stT385o2 254 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 253
    simpa using h
  have hprev := st385o2_p253
  have hstep := st385o2_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p255 : ((1284423835623/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 254, stT385o2 (i+1)) + stT385o2 255 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 254
    simpa using h
  have hprev := st385o2_p254
  have hstep := st385o2_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p256 : ((1354447210623/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 255, stT385o2 (i+1)) + stT385o2 256 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 255
    simpa using h
  have hprev := st385o2_p255
  have hstep := st385o2_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p257 : ((1476034798063/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 256, stT385o2 (i+1)) + stT385o2 257 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 256
    simpa using h
  have hprev := st385o2_p256
  have hstep := st385o2_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p258 : ((7919825003063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 257, stT385o2 (i+1)) + stT385o2 258 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 257
    simpa using h
  have hprev := st385o2_p257
  have hstep := st385o2_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p259 : ((2026475196293/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 258, stT385o2 (i+1)) + stT385o2 259 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 258
    simpa using h
  have hprev := st385o2_p258
  have hstep := st385o2_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p260 : ((3921519707549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 259, stT385o2 (i+1)) + stT385o2 260 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 259
    simpa using h
  have hprev := st385o2_p259
  have hstep := st385o2_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p261 : ((1817873665867/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 260, stT385o2 (i+1)) + stT385o2 261 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 260
    simpa using h
  have hprev := st385o2_p260
  have hstep := st385o2_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p262 : ((6689429713609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 261, stT385o2 (i+1)) + stT385o2 262 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 261
    simpa using h
  have hprev := st385o2_p261
  have hstep := st385o2_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p263 : ((639620075991/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 262, stT385o2 (i+1)) + stT385o2 263 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 262
    simpa using h
  have hprev := st385o2_p262
  have hstep := st385o2_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p264 : ((6539498228677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 263, stT385o2 (i+1)) + stT385o2 264 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 263
    simpa using h
  have hprev := st385o2_p263
  have hstep := st385o2_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p265 : ((7043685764287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 264, stT385o2 (i+1)) + stT385o2 265 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 264
    simpa using h
  have hprev := st385o2_p264
  have hstep := st385o2_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p266 : ((7652596557743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 265, stT385o2 (i+1)) + stT385o2 266 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 265
    simpa using h
  have hprev := st385o2_p265
  have hstep := st385o2_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p267 : ((8061321423123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 266, stT385o2 (i+1)) + stT385o2 267 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 266
    simpa using h
  have hprev := st385o2_p266
  have hstep := st385o2_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p268 : ((2017121206473/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 267, stT385o2 (i+1)) + stT385o2 268 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 267
    simpa using h
  have hprev := st385o2_p267
  have hstep := st385o2_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p269 : ((7673262229449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 268, stT385o2 (i+1)) + stT385o2 269 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 268
    simpa using h
  have hprev := st385o2_p268
  have hstep := st385o2_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p270 : ((883950784081/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 269, stT385o2 (i+1)) + stT385o2 270 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 269
    simpa using h
  have hprev := st385o2_p269
  have hstep := st385o2_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p271 : ((819625947437/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 270, stT385o2 (i+1)) + stT385o2 271 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 270
    simpa using h
  have hprev := st385o2_p270
  have hstep := st385o2_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p272 : ((1594236152179/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 271, stT385o2 (i+1)) + stT385o2 272 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 271
    simpa using h
  have hprev := st385o2_p271
  have hstep := st385o2_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p273 : ((1323071973029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 272, stT385o2 (i+1)) + stT385o2 273 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 272
    simpa using h
  have hprev := st385o2_p272
  have hstep := st385o2_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p274 : ((1431224309957/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 273, stT385o2 (i+1)) + stT385o2 274 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 273
    simpa using h
  have hprev := st385o2_p273
  have hstep := st385o2_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p275 : ((1548386660381/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 274, stT385o2 (i+1)) + stT385o2 275 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 274
    simpa using h
  have hprev := st385o2_p274
  have hstep := st385o2_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p276 : ((8097880404481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 275, stT385o2 (i+1)) + stT385o2 276 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 275
    simpa using h
  have hprev := st385o2_p275
  have hstep := st385o2_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p277 : ((8059765391369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 276, stT385o2 (i+1)) + stT385o2 277 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 276
    simpa using h
  have hprev := st385o2_p276
  have hstep := st385o2_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p278 : ((7647800356167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 277, stT385o2 (i+1)) + stT385o2 278 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 277
    simpa using h
  have hprev := st385o2_p277
  have hstep := st385o2_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p279 : ((7053570769937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 278, stT385o2 (i+1)) + stT385o2 279 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 278
    simpa using h
  have hprev := st385o2_p278
  have hstep := st385o2_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p280 : ((1637301455423/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 279, stT385o2 (i+1)) + stT385o2 280 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 279
    simpa using h
  have hprev := st385o2_p279
  have hstep := st385o2_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p281 : ((3181249696171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 280, stT385o2 (i+1)) + stT385o2 281 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 280
    simpa using h
  have hprev := st385o2_p280
  have hstep := st385o2_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p282 : ((1643835839627/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 281, stT385o2 (i+1)) + stT385o2 282 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 281
    simpa using h
  have hprev := st385o2_p281
  have hstep := st385o2_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p283 : ((3545023208689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 282, stT385o2 (i+1)) + stT385o2 283 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 282
    simpa using h
  have hprev := st385o2_p282
  have hstep := st385o2_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p284 : ((3838137100039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 283, stT385o2 (i+1)) + stT385o2 284 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 283
    simpa using h
  have hprev := st385o2_p283
  have hstep := st385o2_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p285 : ((4037604365559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 284, stT385o2 (i+1)) + stT385o2 285 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 284
    simpa using h
  have hprev := st385o2_p284
  have hstep := st385o2_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p286 : ((4056706404063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 285, stT385o2 (i+1)) + stT385o2 286 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 285
    simpa using h
  have hprev := st385o2_p285
  have hstep := st385o2_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p287 : ((155531745477/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 286, stT385o2 (i+1)) + stT385o2 287 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 286
    simpa using h
  have hprev := st385o2_p286
  have hstep := st385o2_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p288 : ((3606296633913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 287, stT385o2 (i+1)) + stT385o2 288 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 287
    simpa using h
  have hprev := st385o2_p287
  have hstep := st385o2_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p289 : ((133296369857/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 288, stT385o2 (i+1)) + stT385o2 289 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 288
    simpa using h
  have hprev := st385o2_p288
  have hstep := st385o2_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p290 : ((3183295043453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 289, stT385o2 (i+1)) + stT385o2 290 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 289
    simpa using h
  have hprev := st385o2_p289
  have hstep := st385o2_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p291 : ((3221276175563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 290, stT385o2 (i+1)) + stT385o2 291 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 290
    simpa using h
  have hprev := st385o2_p290
  have hstep := st385o2_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p292 : ((3429192489603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 291, stT385o2 (i+1)) + stT385o2 292 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 291
    simpa using h
  have hprev := st385o2_p291
  have hstep := st385o2_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p293 : ((3719099459249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 292, stT385o2 (i+1)) + stT385o2 293 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 292
    simpa using h
  have hprev := st385o2_p292
  have hstep := st385o2_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p294 : ((7940310346471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 293, stT385o2 (i+1)) + stT385o2 294 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 293
    simpa using h
  have hprev := st385o2_p293
  have hstep := st385o2_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p295 : ((8158166174431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 294, stT385o2 (i+1)) + stT385o2 295 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 294
    simpa using h
  have hprev := st385o2_p294
  have hstep := st385o2_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p296 : ((4002147096361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 295, stT385o2 (i+1)) + stT385o2 296 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 295
    simpa using h
  have hprev := st385o2_p295
  have hstep := st385o2_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p297 : ((942953176513/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 296, stT385o2 (i+1)) + stT385o2 297 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 296
    simpa using h
  have hprev := st385o2_p296
  have hstep := st385o2_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p298 : ((1741081048031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 297, stT385o2 (i+1)) + stT385o2 298 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 297
    simpa using h
  have hprev := st385o2_p297
  have hstep := st385o2_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p299 : ((812479143803/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 298, stT385o2 (i+1)) + stT385o2 299 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 298
    simpa using h
  have hprev := st385o2_p298
  have hstep := st385o2_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p300 : ((6334824502571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 299, stT385o2 (i+1)) + stT385o2 300 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 299
    simpa using h
  have hprev := st385o2_p299
  have hstep := st385o2_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p301 : ((6532876717691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 300, stT385o2 (i+1)) + stT385o2 301 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 300
    simpa using h
  have hprev := st385o2_p300
  have hstep := st385o2_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p302 : ((7013703298471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 301, stT385o2 (i+1)) + stT385o2 302 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 301
    simpa using h
  have hprev := st385o2_p301
  have hstep := st385o2_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p303 : ((7587293975851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 302, stT385o2 (i+1)) + stT385o2 303 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 302
    simpa using h
  have hprev := st385o2_p302
  have hstep := st385o2_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p304 : ((8029921552023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 303, stT385o2 (i+1)) + stT385o2 304 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 303
    simpa using h
  have hprev := st385o2_p303
  have hstep := st385o2_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p305 : ((1634255076939/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 304, stT385o2 (i+1)) + stT385o2 305 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 304
    simpa using h
  have hprev := st385o2_p304
  have hstep := st385o2_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p306 : ((318354746079/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 305, stT385o2 (i+1)) + stT385o2 306 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 305
    simpa using h
  have hprev := st385o2_p305
  have hstep := st385o2_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p307 : ((7475926352933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 306, stT385o2 (i+1)) + stT385o2 307 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 306
    simpa using h
  have hprev := st385o2_p306
  have hstep := st385o2_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p308 : ((3453628915353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 307, stT385o2 (i+1)) + stT385o2 308 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 307
    simpa using h
  have hprev := st385o2_p307
  have hstep := st385o2_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p309 : ((1616929688157/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 308, stT385o2 (i+1)) + stT385o2 309 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 308
    simpa using h
  have hprev := st385o2_p308
  have hstep := st385o2_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p310 : ((632116240611/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 309, stT385o2 (i+1)) + stT385o2 310 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 309
    simpa using h
  have hprev := st385o2_p309
  have hstep := st385o2_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p311 : ((326019151431/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 310, stT385o2 (i+1)) + stT385o2 311 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 310
    simpa using h
  have hprev := st385o2_p310
  have hstep := st385o2_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p312 : ((3494792590923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 311, stT385o2 (i+1)) + stT385o2 312 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 311
    simpa using h
  have hprev := st385o2_p311
  have hstep := st385o2_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p313 : ((1510930061529/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 312, stT385o2 (i+1)) + stT385o2 313 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 312
    simpa using h
  have hprev := st385o2_p312
  have hstep := st385o2_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p314 : ((8008531812937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 313, stT385o2 (i+1)) + stT385o2 314 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 313
    simpa using h
  have hprev := st385o2_p313
  have hstep := st385o2_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p315 : ((8187054819229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 314, stT385o2 (i+1)) + stT385o2 315 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 314
    simpa using h
  have hprev := st385o2_p314
  have hstep := st385o2_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p316 : ((8027410457469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 315, stT385o2 (i+1)) + stT385o2 316 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 315
    simpa using h
  have hprev := st385o2_p315
  have hstep := st385o2_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p317 : ((1517771756241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 316, stT385o2 (i+1)) + stT385o2 317 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 316
    simpa using h
  have hprev := st385o2_p316
  have hstep := st385o2_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p318 : ((7029376680651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 317, stT385o2 (i+1)) + stT385o2 318 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 317
    simpa using h
  have hprev := st385o2_p317
  have hstep := st385o2_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p319 : ((6547921330593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 318, stT385o2 (i+1)) + stT385o2 319 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 318
    simpa using h
  have hprev := st385o2_p318
  have hstep := st385o2_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p320 : ((98649770583/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 319, stT385o2 (i+1)) + stT385o2 320 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 319
    simpa using h
  have hprev := st385o2_p319
  have hstep := st385o2_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p321 : ((100108761613/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 320, stT385o2 (i+1)) + stT385o2 321 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 320
    simpa using h
  have hprev := st385o2_p320
  have hstep := st385o2_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p322 : ((3396813763127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 321, stT385o2 (i+1)) + stT385o2 322 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 321
    simpa using h
  have hprev := st385o2_p321
  have hstep := st385o2_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p323 : ((1834533705767/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 322, stT385o2 (i+1)) + stT385o2 323 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 322
    simpa using h
  have hprev := st385o2_p322
  have hstep := st385o2_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p324 : ((7852354864403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 323, stT385o2 (i+1)) + stT385o2 324 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 323
    simpa using h
  have hprev := st385o2_p323
  have hstep := st385o2_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p325 : ((8160726461903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 324, stT385o2 (i+1)) + stT385o2 325 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 324
    simpa using h
  have hprev := st385o2_p324
  have hstep := st385o2_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p326 : ((4079833474383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 325, stT385o2 (i+1)) + stT385o2 326 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 325
    simpa using h
  have hprev := st385o2_p325
  have hstep := st385o2_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p327 : ((1962825908133/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 326, stT385o2 (i+1)) + stT385o2 327 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 326
    simpa using h
  have hprev := st385o2_p326
  have hstep := st385o2_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p328 : ((917613167759/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 327, stT385o2 (i+1)) + stT385o2 328 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 327
    simpa using h
  have hprev := st385o2_p327
  have hstep := st385o2_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p329 : ((3399974681941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 328, stT385o2 (i+1)) + stT385o2 329 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 328
    simpa using h
  have hprev := st385o2_p328
  have hstep := st385o2_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p330 : ((3204029513077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 329, stT385o2 (i+1)) + stT385o2 330 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 329
    simpa using h
  have hprev := st385o2_p329
  have hstep := st385o2_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p331 : ((3146809848777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 330, stT385o2 (i+1)) + stT385o2 331 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 330
    simpa using h
  have hprev := st385o2_p330
  have hstep := st385o2_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p332 : ((6492570054159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 331, stT385o2 (i+1)) + stT385o2 332 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 331
    simpa using h
  have hprev := st385o2_p331
  have hstep := st385o2_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p333 : ((6938276024807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 332, stT385o2 (i+1)) + stT385o2 333 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 332
    simpa using h
  have hprev := st385o2_p332
  have hstep := st385o2_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p334 : ((7484902755457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 333, stT385o2 (i+1)) + stT385o2 334 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 333
    simpa using h
  have hprev := st385o2_p333
  have hstep := st385o2_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p335 : ((7955761182511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 334, stT385o2 (i+1)) + stT385o2 335 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 334
    simpa using h
  have hprev := st385o2_p334
  have hstep := st385o2_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p336 : ((1640089824587/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 335, stT385o2 (i+1)) + stT385o2 336 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 335
    simpa using h
  have hprev := st385o2_p335
  have hstep := st385o2_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p337 : ((1628459514443/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 336, stT385o2 (i+1)) + stT385o2 337 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 336
    simpa using h
  have hprev := st385o2_p336
  have hstep := st385o2_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p338 : ((3900705098419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 337, stT385o2 (i+1)) + stT385o2 338 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 337
    simpa using h
  have hprev := st385o2_p337
  have hstep := st385o2_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p339 : ((1821664953677/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 338, stT385o2 (i+1)) + stT385o2 339 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 338
    simpa using h
  have hprev := st385o2_p338
  have hstep := st385o2_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p340 : ((845016485609/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 339, stT385o2 (i+1)) + stT385o2 340 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 339
    simpa using h
  have hprev := st385o2_p339
  have hstep := st385o2_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p341 : ((1277149210523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 340, stT385o2 (i+1)) + stT385o2 341 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 340
    simpa using h
  have hprev := st385o2_p340
  have hstep := st385o2_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p342 : ((1569627619827/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 341, stT385o2 (i+1)) + stT385o2 342 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 341
    simpa using h
  have hprev := st385o2_p341
  have hstep := st385o2_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p343 : ((1293986963727/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 342, stT385o2 (i+1)) + stT385o2 343 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 342
    simpa using h
  have hprev := st385o2_p342
  have hstep := st385o2_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p344 : ((1724950078191/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 343, stT385o2 (i+1)) + stT385o2 344 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 343
    simpa using h
  have hprev := st385o2_p343
  have hstep := st385o2_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p345 : ((7436016482763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 344, stT385o2 (i+1)) + stT385o2 345 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 344
    simpa using h
  have hprev := st385o2_p344
  have hstep := st385o2_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p346 : ((7915783076817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 345, stT385o2 (i+1)) + stT385o2 346 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 345
    simpa using h
  have hprev := st385o2_p345
  have hstep := st385o2_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p347 : ((1639016360269/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 346, stT385o2 (i+1)) + stT385o2 347 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 346
    simpa using h
  have hprev := st385o2_p346
  have hstep := st385o2_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p348 : ((8191450551227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 347, stT385o2 (i+1)) + stT385o2 348 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 347
    simpa using h
  have hprev := st385o2_p347
  have hstep := st385o2_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p349 : ((7907493114139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 348, stT385o2 (i+1)) + stT385o2 349 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 348
    simpa using h
  have hprev := st385o2_p348
  have hstep := st385o2_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p350 : ((464295154163/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 349, stT385o2 (i+1)) + stT385o2 350 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 349
    simpa using h
  have hprev := st385o2_p349
  have hstep := st385o2_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p351 : ((275880593807/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 350, stT385o2 (i+1)) + stT385o2 351 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 350
    simpa using h
  have hprev := st385o2_p350
  have hstep := st385o2_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p352 : ((6468184888063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 351, stT385o2 (i+1)) + stT385o2 352 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 351
    simpa using h
  have hprev := st385o2_p351
  have hstep := st385o2_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p353 : ((783303052629/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 352, stT385o2 (i+1)) + stT385o2 353 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 352
    simpa using h
  have hprev := st385o2_p352
  have hstep := st385o2_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p354 : ((3174440997337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 353, stT385o2 (i+1)) + stT385o2 354 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 353
    simpa using h
  have hprev := st385o2_p353
  have hstep := st385o2_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p355 : ((3345146843777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 354, stT385o2 (i+1)) + stT385o2 355 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 354
    simpa using h
  have hprev := st385o2_p354
  have hstep := st385o2_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p356 : ((449474220367/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 355, stT385o2 (i+1)) + stT385o2 356 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 355
    simpa using h
  have hprev := st385o2_p355
  have hstep := st385o2_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p357 : ((240913919059/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 356, stT385o2 (i+1)) + stT385o2 357 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 356
    simpa using h
  have hprev := st385o2_p356
  have hstep := st385o2_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p358 : ((1012082936671/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 357, stT385o2 (i+1)) + stT385o2 358 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 357
    simpa using h
  have hprev := st385o2_p357
  have hstep := st385o2_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p359 : ((1030683979747/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 358, stT385o2 (i+1)) + stT385o2 359 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 358
    simpa using h
  have hprev := st385o2_p358
  have hstep := st385o2_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p360 : ((1623051605003/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 359, stT385o2 (i+1)) + stT385o2 360 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 359
    simpa using h
  have hprev := st385o2_p359
  have hstep := st385o2_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p361 : ((309749999267/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 360, stT385o2 (i+1)) + stT385o2 361 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 360
    simpa using h
  have hprev := st385o2_p360
  have hstep := st385o2_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p362 : ((7235092305721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 361, stT385o2 (i+1)) + stT385o2 362 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 361
    simpa using h
  have hprev := st385o2_p361
  have hstep := st385o2_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p363 : ((6730112253497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 362, stT385o2 (i+1)) + stT385o2 363 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 362
    simpa using h
  have hprev := st385o2_p362
  have hstep := st385o2_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p364 : ((6367131694851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 363, stT385o2 (i+1)) + stT385o2 364 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 363
    simpa using h
  have hprev := st385o2_p363
  have hstep := st385o2_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p365 : ((1248864249031/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 364, stT385o2 (i+1)) + stT385o2 365 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 364
    simpa using h
  have hprev := st385o2_p364
  have hstep := st385o2_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p366 : ((6393711714263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 365, stT385o2 (i+1)) + stT385o2 366 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 365
    simpa using h
  have hprev := st385o2_p365
  have hstep := st385o2_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p367 : ((3386800702719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 366, stT385o2 (i+1)) + stT385o2 367 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 366
    simpa using h
  have hprev := st385o2_p366
  have hstep := st385o2_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p368 : ((145618255407/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 367, stT385o2 (i+1)) + stT385o2 368 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 367
    simpa using h
  have hprev := st385o2_p367
  have hstep := st385o2_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p369 : ((7779648796089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 368, stT385o2 (i+1)) + stT385o2 369 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 368
    simpa using h
  have hprev := st385o2_p368
  have hstep := st385o2_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p370 : ((8137504752339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 369, stT385o2 (i+1)) + stT385o2 370 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 369
    simpa using h
  have hprev := st385o2_p369
  have hstep := st385o2_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p371 : ((1652149670631/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 370, stT385o2 (i+1)) + stT385o2 371 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 370
    simpa using h
  have hprev := st385o2_p370
  have hstep := st385o2_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p372 : ((8118212042091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 371, stT385o2 (i+1)) + stT385o2 372 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 371
    simpa using h
  have hprev := st385o2_p371
  have hstep := st385o2_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p373 : ((3874238269477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 372, stT385o2 (i+1)) + stT385o2 373 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 372
    simpa using h
  have hprev := st385o2_p372
  have hstep := st385o2_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p374 : ((724876631537/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 373, stT385o2 (i+1)) + stT385o2 374 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 373
    simpa using h
  have hprev := st385o2_p373
  have hstep := st385o2_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p375 : ((210902859443/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 374, stT385o2 (i+1)) + stT385o2 375 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 374
    simpa using h
  have hprev := st385o2_p374
  have hstep := st385o2_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p376 : ((6377375876331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 375, stT385o2 (i+1)) + stT385o2 376 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 375
    simpa using h
  have hprev := st385o2_p375
  have hstep := st385o2_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p377 : ((6228587666193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 376, stT385o2 (i+1)) + stT385o2 377 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 376
    simpa using h
  have hprev := st385o2_p376
  have hstep := st385o2_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p378 : ((6339257007297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 377, stT385o2 (i+1)) + stT385o2 378 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 377
    simpa using h
  have hprev := st385o2_p377
  have hstep := st385o2_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p379 : ((3340029932921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 378, stT385o2 (i+1)) + stT385o2 379 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 378
    simpa using h
  have hprev := st385o2_p378
  have hstep := st385o2_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p380 : ((3581995558463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 379, stT385o2 (i+1)) + stT385o2 380 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 379
    simpa using h
  have hprev := st385o2_p379
  have hstep := st385o2_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p381 : ((7669078889221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 380, stT385o2 (i+1)) + stT385o2 381 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 380
    simpa using h
  have hprev := st385o2_p380
  have hstep := st385o2_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p382 : ((1613861049041/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 381, stT385o2 (i+1)) + stT385o2 382 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 381
    simpa using h
  have hprev := st385o2_p381
  have hstep := st385o2_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p383 : ((8265943117333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 382, stT385o2 (i+1)) + stT385o2 383 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 382
    simpa using h
  have hprev := st385o2_p382
  have hstep := st385o2_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p384 : ((8211475583059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 383, stT385o2 (i+1)) + stT385o2 384 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 383
    simpa using h
  have hprev := st385o2_p383
  have hstep := st385o2_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p385 : ((7920517030211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 384, stT385o2 (i+1)) + stT385o2 385 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 384
    simpa using h
  have hprev := st385o2_p384
  have hstep := st385o2_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p386 : ((7465299416891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 385, stT385o2 (i+1)) + stT385o2 386 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 385
    simpa using h
  have hprev := st385o2_p385
  have hstep := st385o2_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p387 : ((869655169531/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 386, stT385o2 (i+1)) + stT385o2 387 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 386
    simpa using h
  have hprev := st385o2_p386
  have hstep := st385o2_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p388 : ((1629857601521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 387, stT385o2 (i+1)) + stT385o2 388 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 387
    simpa using h
  have hprev := st385o2_p387
  have hstep := st385o2_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p389 : ((3128414509777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 388, stT385o2 (i+1)) + stT385o2 389 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 388
    simpa using h
  have hprev := st385o2_p388
  have hstep := st385o2_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p390 : ((1557855476201/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 389, stT385o2 (i+1)) + stT385o2 390 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 389
    simpa using h
  have hprev := st385o2_p389
  have hstep := st385o2_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p391 : ((403005433837/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 390, stT385o2 (i+1)) + stT385o2 391 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 390
    simpa using h
  have hprev := st385o2_p390
  have hstep := st385o2_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p392 : ((1370859671/2000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 391, stT385o2 (i+1)) + stT385o2 392 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 391
    simpa using h
  have hprev := st385o2_p391
  have hstep := st385o2_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p393 : ((1470670315411/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 392, stT385o2 (i+1)) + stT385o2 393 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 392
    simpa using h
  have hprev := st385o2_p392
  have hstep := st385o2_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p394 : ((7827710537039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 393, stT385o2 (i+1)) + stT385o2 394 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 393
    simpa using h
  have hprev := st385o2_p393
  have hstep := st385o2_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p395 : ((8166763375709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 394, stT385o2 (i+1)) + stT385o2 395 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 394
    simpa using h
  have hprev := st385o2_p394
  have hstep := st385o2_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p396 : ((8292399408443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 395, stT385o2 (i+1)) + stT385o2 396 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 395
    simpa using h
  have hprev := st385o2_p395
  have hstep := st385o2_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p397 : ((8176617319559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 396, stT385o2 (i+1)) + stT385o2 397 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 396
    simpa using h
  have hprev := st385o2_p396
  have hstep := st385o2_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p398 : ((7847192533559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 397, stT385o2 (i+1)) + stT385o2 398 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 397
    simpa using h
  have hprev := st385o2_p397
  have hstep := st385o2_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p399 : ((1476109418613/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 398, stT385o2 (i+1)) + stT385o2 399 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 398
    simpa using h
  have hprev := st385o2_p398
  have hstep := st385o2_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p400 : ((1376721219837/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 399, stT385o2 (i+1)) + stT385o2 400 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 399
    simpa using h
  have hprev := st385o2_p399
  have hstep := st385o2_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p401 : ((3234563841789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 400, stT385o2 (i+1)) + stT385o2 401 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 400
    simpa using h
  have hprev := st385o2_p400
  have hstep := st385o2_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p402 : ((6230178651873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 401, stT385o2 (i+1)) + stT385o2 402 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 401
    simpa using h
  have hprev := st385o2_p401
  have hstep := st385o2_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p403 : ((6219546437089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 402, stT385o2 (i+1)) + stT385o2 403 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 402
    simpa using h
  have hprev := st385o2_p402
  have hstep := st385o2_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p404 : ((6438509581587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 403, stT385o2 (i+1)) + stT385o2 404 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 403
    simpa using h
  have hprev := st385o2_p403
  have hstep := st385o2_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p405 : ((8546636899/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 404, stT385o2 (i+1)) + stT385o2 405 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 404
    simpa using h
  have hprev := st385o2_p404
  have hstep := st385o2_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p406 : ((7326884213097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 405, stT385o2 (i+1)) + stT385o2 406 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 405
    simpa using h
  have hprev := st385o2_p405
  have hstep := st385o2_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p407 : ((3899520344259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 406, stT385o2 (i+1)) + stT385o2 407 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 406
    simpa using h
  have hprev := st385o2_p406
  have hstep := st385o2_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p408 : ((8150430136947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 407, stT385o2 (i+1)) + stT385o2 408 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 407
    simpa using h
  have hprev := st385o2_p407
  have hstep := st385o2_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p409 : ((8305013195447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 408, stT385o2 (i+1)) + stT385o2 409 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 408
    simpa using h
  have hprev := st385o2_p408
  have hstep := st385o2_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p410 : ((8230171905617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 409, stT385o2 (i+1)) + stT385o2 410 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 409
    simpa using h
  have hprev := st385o2_p409
  have hstep := st385o2_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p411 : ((7943131225473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 410, stT385o2 (i+1)) + stT385o2 411 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 410
    simpa using h
  have hprev := st385o2_p410
  have hstep := st385o2_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p412 : ((3753282748179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 411, stT385o2 (i+1)) + stT385o2 412 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 411
    simpa using h
  have hprev := st385o2_p411
  have hstep := st385o2_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p413 : ((3507265232457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 412, stT385o2 (i+1)) + stT385o2 413 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 412
    simpa using h
  have hprev := st385o2_p412
  have hstep := st385o2_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p414 : ((1643001941697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 413, stT385o2 (i+1)) + stT385o2 414 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 413
    simpa using h
  have hprev := st385o2_p413
  have hstep := st385o2_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p415 : ((6272512923711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 414, stT385o2 (i+1)) + stT385o2 415 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 414
    simpa using h
  have hprev := st385o2_p414
  have hstep := st385o2_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p416 : ((1544629441307/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 415, stT385o2 (i+1)) + stT385o2 416 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 415
    simpa using h
  have hprev := st385o2_p415
  have hstep := st385o2_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p417 : ((788599883089/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 416, stT385o2 (i+1)) + stT385o2 417 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 416
    simpa using h
  have hprev := st385o2_p416
  have hstep := st385o2_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p418 : ((6635100887317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 417, stT385o2 (i+1)) + stT385o2 418 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 417
    simpa using h
  have hprev := st385o2_p417
  have hstep := st385o2_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p419 : ((7088684333701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 418, stT385o2 (i+1)) + stT385o2 419 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 418
    simpa using h
  have hprev := st385o2_p418
  have hstep := st385o2_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p420 : ((7575108026101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 419, stT385o2 (i+1)) + stT385o2 420 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 419
    simpa using h
  have hprev := st385o2_p419
  have hstep := st385o2_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p421 : ((7994039093851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 420, stT385o2 (i+1)) + stT385o2 421 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 420
    simpa using h
  have hprev := st385o2_p420
  have hstep := st385o2_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p422 : ((1651980790439/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 421, stT385o2 (i+1)) + stT385o2 422 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 421
    simpa using h
  have hprev := st385o2_p421
  have hstep := st385o2_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p423 : ((8319157151251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 422, stT385o2 (i+1)) + stT385o2 423 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 422
    simpa using h
  have hprev := st385o2_p422
  have hstep := st385o2_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p424 : ((8160693782923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 423, stT385o2 (i+1)) + stT385o2 424 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 423
    simpa using h
  have hprev := st385o2_p423
  have hstep := st385o2_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p425 : ((7817533477099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 424, stT385o2 (i+1)) + stT385o2 425 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 424
    simpa using h
  have hprev := st385o2_p424
  have hstep := st385o2_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p426 : ((7359556508093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 425, stT385o2 (i+1)) + stT385o2 426 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 425
    simpa using h
  have hprev := st385o2_p425
  have hstep := st385o2_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p427 : ((6879007626423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 426, stT385o2 (i+1)) + stT385o2 427 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 426
    simpa using h
  have hprev := st385o2_p426
  have hstep := st385o2_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p428 : ((25280418471/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 427, stT385o2 (i+1)) + stT385o2 428 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 427
    simpa using h
  have hprev := st385o2_p427
  have hstep := st385o2_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p429 : ((6218383544691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 428, stT385o2 (i+1)) + stT385o2 429 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 428
    simpa using h
  have hprev := st385o2_p428
  have hstep := st385o2_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p430 : ((1233631394351/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 429, stT385o2 (i+1)) + stT385o2 430 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 429
    simpa using h
  have hprev := st385o2_p429
  have hstep := st385o2_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p431 : ((3165030371699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 430, stT385o2 (i+1)) + stT385o2 431 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 430
    simpa using h
  have hprev := st385o2_p430
  have hstep := st385o2_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p432 : ((3335727748199/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 431, stT385o2 (i+1)) + stT385o2 432 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 431
    simpa using h
  have hprev := st385o2_p431
  have hstep := st385o2_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p433 : ((1781252928227/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 432, stT385o2 (i+1)) + stT385o2 433 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 432
    simpa using h
  have hprev := st385o2_p432
  have hstep := st385o2_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p434 : ((950280088231/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 433, stT385o2 (i+1)) + stT385o2 434 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 433
    simpa using h
  have hprev := st385o2_p433
  have hstep := st385o2_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p435 : ((8010878869877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 434, stT385o2 (i+1)) + stT385o2 435 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 434
    simpa using h
  have hprev := st385o2_p434
  have hstep := st385o2_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p436 : ((4136337133381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 435, stT385o2 (i+1)) + stT385o2 436 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 435
    simpa using h
  have hprev := st385o2_p435
  have hstep := st385o2_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p437 : ((4169088563823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 436, stT385o2 (i+1)) + stT385o2 437 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 436
    simpa using h
  have hprev := st385o2_p436
  have hstep := st385o2_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p438 : ((4097880153891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 437, stT385o2 (i+1)) + stT385o2 438 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 437
    simpa using h
  have hprev := st385o2_p437
  have hstep := st385o2_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p439 : ((157467062597/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 438, stT385o2 (i+1)) + stT385o2 439 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 438
    simpa using h
  have hprev := st385o2_p438
  have hstep := st385o2_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p440 : ((3716306721193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 439, stT385o2 (i+1)) + stT385o2 440 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 439
    simpa using h
  have hprev := st385o2_p439
  have hstep := st385o2_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p441 : ((1739224420251/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 440, stT385o2 (i+1)) + stT385o2 441 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 440
    simpa using h
  have hprev := st385o2_p440
  have hstep := st385o2_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p442 : ((1633842530521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 441, stT385o2 (i+1)) + stT385o2 442 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 441
    simpa using h
  have hprev := st385o2_p441
  have hstep := st385o2_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p443 : ((1561579439481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 442, stT385o2 (i+1)) + stT385o2 443 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 442
    simpa using h
  have hprev := st385o2_p442
  have hstep := st385o2_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p444 : ((6142767942177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 443, stT385o2 (i+1)) + stT385o2 444 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 443
    simpa using h
  have hprev := st385o2_p443
  have hstep := st385o2_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p445 : ((1560756522363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 444, stT385o2 (i+1)) + stT385o2 445 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 444
    simpa using h
  have hprev := st385o2_p444
  have hstep := st385o2_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p446 : ((6527776446593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 445, stT385o2 (i+1)) + stT385o2 446 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 445
    simpa using h
  have hprev := st385o2_p445
  have hstep := st385o2_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p447 : ((6944095137227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 446, stT385o2 (i+1)) + stT385o2 447 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 446
    simpa using h
  have hprev := st385o2_p446
  have hstep := st385o2_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p448 : ((7415552312267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 447, stT385o2 (i+1)) + stT385o2 448 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 447
    simpa using h
  have hprev := st385o2_p447
  have hstep := st385o2_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p449 : ((7856374584161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 448, stT385o2 (i+1)) + stT385o2 449 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 448
    simpa using h
  have hprev := st385o2_p448
  have hstep := st385o2_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p450 : ((8187066375777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 449, stT385o2 (i+1)) + stT385o2 450 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 449
    simpa using h
  have hprev := st385o2_p449
  have hstep := st385o2_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p451 : ((8348623763353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 450, stT385o2 (i+1)) + stT385o2 451 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 450
    simpa using h
  have hprev := st385o2_p450
  have hstep := st385o2_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p452 : ((2078211908833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 451, stT385o2 (i+1)) + stT385o2 452 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 451
    simpa using h
  have hprev := st385o2_p451
  have hstep := st385o2_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p453 : ((2021737020633/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 452, stT385o2 (i+1)) + stT385o2 453 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 452
    simpa using h
  have hprev := st385o2_p452
  have hstep := st385o2_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p454 : ((481989908057/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 453, stT385o2 (i+1)) + stT385o2 454 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 453
    simpa using h
  have hprev := st385o2_p453
  have hstep := st385o2_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p455 : ((226701144611/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 454, stT385o2 (i+1)) + stT385o2 455 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 454
    simpa using h
  have hprev := st385o2_p454
  have hstep := st385o2_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p456 : ((849447583511/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 455, stT385o2 (i+1)) + stT385o2 456 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 455
    simpa using h
  have hprev := st385o2_p455
  have hstep := st385o2_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p457 : ((6415662505537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 456, stT385o2 (i+1)) + stT385o2 457 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 456
    simpa using h
  have hprev := st385o2_p456
  have hstep := st385o2_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p458 : ((6180624760997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 457, stT385o2 (i+1)) + stT385o2 458 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 457
    simpa using h
  have hprev := st385o2_p457
  have hstep := st385o2_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p459 : ((6130684134563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 458, stT385o2 (i+1)) + stT385o2 459 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 458
    simpa using h
  have hprev := st385o2_p458
  have hstep := st385o2_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p460 : ((6273680359199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 459, stT385o2 (i+1)) + stT385o2 460 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 459
    simpa using h
  have hprev := st385o2_p459
  have hstep := st385o2_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p461 : ((6584180176511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 460, stT385o2 (i+1)) + stT385o2 461 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 460
    simpa using h
  have hprev := st385o2_p460
  have hstep := st385o2_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p462 : ((7008224066927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 461, stT385o2 (i+1)) + stT385o2 462 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 461
    simpa using h
  have hprev := st385o2_p461
  have hstep := st385o2_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p463 : ((3736463176273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 462, stT385o2 (i+1)) + stT385o2 463 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 462
    simpa using h
  have hprev := st385o2_p462
  have hstep := st385o2_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p464 : ((3949548882511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 463, stT385o2 (i+1)) + stT385o2 464 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 463
    simpa using h
  have hprev := st385o2_p463
  have hstep := st385o2_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p465 : ((205368421527/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 464, stT385o2 (i+1)) + stT385o2 465 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 464
    simpa using h
  have hprev := st385o2_p464
  have hstep := st385o2_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p466 : ((8367090803847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 465, stT385o2 (i+1)) + stT385o2 466 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 465
    simpa using h
  have hprev := st385o2_p465
  have hstep := st385o2_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p467 : ((8331256756537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 466, stT385o2 (i+1)) + stT385o2 467 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 466
    simpa using h
  have hprev := st385o2_p466
  have hstep := st385o2_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p468 : ((8114003409047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 467, stT385o2 (i+1)) + stT385o2 468 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 467
    simpa using h
  have hprev := st385o2_p467
  have hstep := st385o2_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p469 : ((7752240027463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 468, stT385o2 (i+1)) + stT385o2 469 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 468
    simpa using h
  have hprev := st385o2_p468
  have hstep := st385o2_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p470 : ((7306534374707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 469, stT385o2 (i+1)) + stT385o2 470 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 469
    simpa using h
  have hprev := st385o2_p469
  have hstep := st385o2_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p471 : ((6850803871907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 470, stT385o2 (i+1)) + stT385o2 471 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 470
    simpa using h
  have hprev := st385o2_p470
  have hstep := st385o2_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p472 : ((1292000742023/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 471, stT385o2 (i+1)) + stT385o2 472 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 471
    simpa using h
  have hprev := st385o2_p471
  have hstep := st385o2_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p473 : ((193682453567/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 472, stT385o2 (i+1)) + stT385o2 473 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 472
    simpa using h
  have hprev := st385o2_p472
  have hstep := st385o2_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p474 : ((763315237523/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 473, stT385o2 (i+1)) + stT385o2 474 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 473
    simpa using h
  have hprev := st385o2_p473
  have hstep := st385o2_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p475 : ((6200171601439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 474, stT385o2 (i+1)) + stT385o2 475 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 474
    simpa using h
  have hprev := st385o2_p474
  have hstep := st385o2_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p476 : ((6462882581071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 475, stT385o2 (i+1)) + stT385o2 476 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 475
    simpa using h
  have hprev := st385o2_p475
  have hstep := st385o2_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p477 : ((1370333308299/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 476, stT385o2 (i+1)) + stT385o2 477 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 476
    simpa using h
  have hprev := st385o2_p476
  have hstep := st385o2_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p478 : ((1825918361283/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 477, stT385o2 (i+1)) + stT385o2 478 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 477
    simpa using h
  have hprev := st385o2_p477
  have hstep := st385o2_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p479 : ((7746464524499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 478, stT385o2 (i+1)) + stT385o2 479 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 478
    simpa using h
  have hprev := st385o2_p478
  have hstep := st385o2_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p480 : ((4054827893827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 479, stT385o2 (i+1)) + stT385o2 480 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 479
    simpa using h
  have hprev := st385o2_p479
  have hstep := st385o2_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p481 : ((4168026803227/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 480, stT385o2 (i+1)) + stT385o2 481 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 480
    simpa using h
  have hprev := st385o2_p480
  have hstep := st385o2_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p482 : ((8390491135259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 481, stT385o2 (i+1)) + stT385o2 482 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 481
    simpa using h
  have hprev := st385o2_p481
  have hstep := st385o2_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p483 : ((8265113751539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 482, stT385o2 (i+1)) + stT385o2 483 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 482
    simpa using h
  have hprev := st385o2_p482
  have hstep := st385o2_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p484 : ((1596049591031/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 483, stT385o2 (i+1)) + stT385o2 484 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 483
    simpa using h
  have hprev := st385o2_p483
  have hstep := st385o2_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p485 : ((7580919927199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 484, stT385o2 (i+1)) + stT385o2 485 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 484
    simpa using h
  have hprev := st385o2_p484
  have hstep := st385o2_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p486 : ((7129541234789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 485, stT385o2 (i+1)) + stT385o2 486 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 485
    simpa using h
  have hprev := st385o2_p485
  have hstep := st385o2_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p487 : ((6696075012989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 486, stT385o2 (i+1)) + stT385o2 487 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 486
    simpa using h
  have hprev := st385o2_p486
  have hstep := st385o2_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p488 : ((3173582036419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 487, stT385o2 (i+1)) + stT385o2 488 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 487
    simpa using h
  have hprev := st385o2_p487
  have hstep := st385o2_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p489 : ((613594618907/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 488, stT385o2 (i+1)) + stT385o2 489 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 488
    simpa using h
  have hprev := st385o2_p488
  have hstep := st385o2_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p490 : ((1523530587999/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 489, stT385o2 (i+1)) + stT385o2 490 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 489
    simpa using h
  have hprev := st385o2_p489
  have hstep := st385o2_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p491 : ((6227382405501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 490, stT385o2 (i+1)) + stT385o2 491 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 490
    simpa using h
  have hprev := st385o2_p490
  have hstep := st385o2_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p492 : ((6514841828079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 491, stT385o2 (i+1)) + stT385o2 492 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 491
    simpa using h
  have hprev := st385o2_p491
  have hstep := st385o2_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p493 : ((276500952733/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 492, stT385o2 (i+1)) + stT385o2 493 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 492
    simpa using h
  have hprev := st385o2_p492
  have hstep := st385o2_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p494 : ((3680123027199/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 493, stT385o2 (i+1)) + stT385o2 494 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 493
    simpa using h
  have hprev := st385o2_p493
  have hstep := st385o2_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p495 : ((1947702215709/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 494, stT385o2 (i+1)) + stT385o2 495 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 494
    simpa using h
  have hprev := st385o2_p494
  have hstep := st385o2_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p496 : ((2035025365923/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 495, stT385o2 (i+1)) + stT385o2 496 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 495
    simpa using h
  have hprev := st385o2_p495
  have hstep := st385o2_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p497 : ((1044573246689/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 496, stT385o2 (i+1)) + stT385o2 497 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 496
    simpa using h
  have hprev := st385o2_p496
  have hstep := st385o2_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p498 : ((4204386656111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 497, stT385o2 (i+1)) + stT385o2 498 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 497
    simpa using h
  have hprev := st385o2_p497
  have hstep := st385o2_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p499 : ((2072403324519/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 498, stT385o2 (i+1)) + stT385o2 499 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 498
    simpa using h
  have hprev := st385o2_p498
  have hstep := st385o2_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_p500 : ((1002156266671/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT385o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT385o2 (i+1))
      = (∑ i ∈ Finset.range 499, stT385o2 (i+1)) + stT385o2 500 := by
    have h := Finset.sum_range_succ (fun i => stT385o2 (i+1)) 499
    simpa using h
  have hprev := st385o2_p499
  have hstep := st385o2_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st385o2_s500 :
    |Real.sin (((385 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))
      - ((99149/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log ((500 : ℕ)) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((500 : ℕ)) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact sinMulShift_eval (r := 5563901/10000000) (δ := 4883/500000000) (ψ := 281281/1000000) 385 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 385/2`** (evaluated boundary). -/
theorem station_385o2_sign : 0 < hardyG (((((385:ℕ)):ℝ)/2)) := by
  have hcore := phase_station_lower_half_eval 385 500 (by norm_num) (by norm_num)
    ((281281/1000000 : ℚ) : ℝ)
  have hchain := st385o2_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT385o2 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((385 : ℕ) : ℝ) * (Real.log ((i+1 : ℕ)) / 2)
              - ((281281/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st385o2_c500
  have hsinb := abs_le.mp st385o2_s500
  have hbdy_lo : ((-266222692881/2895039062500 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((385 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ))) / 2
          - ((((385:ℕ)):ℝ)/2)
            * Real.sin (((385 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((281281/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((385:ℕ)):ℝ)/2) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((385:ℝ) * (Real.log (500:ℝ) / 2) - ((281281/1000000 : ℚ) : ℝ))) / 2
        - ((385:ℝ)/2) * Real.sin ((385:ℝ) * (Real.log (500:ℝ) / 2) - ((281281/1000000 : ℚ) : ℝ))
        ≥ ((-2381166/15625 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((385:ℝ)/2) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-2381166/15625 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-2381166/15625 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-2381166/15625 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((385:ℕ)):ℝ)/2)+1) * (((((385:ℕ)):ℝ)/2)+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((12148913335601/40000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1002156266671/1250000000000 : ℚ) : ℝ) + ((-266222692881/2895039062500 : ℚ) : ℝ)
      - ((12148913335601/40000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((281281/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line (((((385:ℕ)):ℝ)/2)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((281281/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((((385:ℕ)):ℝ)/2)))).re
      - Real.sin ((281281/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((((385:ℕ)):ℝ)/2)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((((385:ℕ)):ℝ)/2))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((((385:ℕ)):ℝ)/2))
      = ((((((385:ℕ)):ℝ)/2)) * (Real.log (((((385:ℕ)):ℝ)/2)) - Real.log 2
          - Real.log Real.pi) - (((((385:ℕ)):ℝ)/2))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM : ((52600961/10000000 : ℚ) : ℝ) ≤ Real.log (((((385:ℕ)):ℝ)/2))
      ∧ Real.log (((((385:ℕ)):ℝ)/2)) ≤ ((52600963/10000000 : ℚ) : ℝ) := by
    have hsplit : Real.log (((((385:ℕ)):ℝ)/2))
        = Real.log ((((385:ℕ)):ℝ)) - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    have hM := log_br_385
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
  have hθwin : |(((281281/1000000 : ℚ) : ℝ) + ((37:ℤ)) * (2*Real.pi)) - theta (((((385:ℕ)):ℝ)/2))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((((385:ℕ)):ℝ)/2)))
    (φ := ((281281/1000000 : ℚ) : ℝ) + ((37:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((281281/1000000 : ℚ)) : ℝ) 37).1,
    (cos_sin_shift (((281281/1000000 : ℚ)) : ℝ) 37).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_385o2_sign
end AxiomAudit
