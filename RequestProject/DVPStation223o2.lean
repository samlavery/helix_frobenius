import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationHalfEval

/-!
# Station `t = 223/2` (rung-126; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT223o2 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((223 : ℕ) : ℝ) * (Real.log ((n : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))

theorem st223o2_c1 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((862729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((0 : ℚ) : ℝ) ≤ Real.log ((1 : ℕ)) / 2 := by
    have h := (log_br_1).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((1 : ℕ)) / 2 ≤ ((0 : ℚ) : ℝ) := by
    have h := (log_br_1).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -331347/2500000) (δ := 21/100000000) (ψ := 106031/200000) 223 0
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t1 : ((862679/1000000 : ℚ) : ℝ) ≤ stT223o2 1 := by
  have hc : ((862679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((862679/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((862679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c2 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((52913/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log ((2 : ℕ)) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((2 : ℕ)) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3393829/10000000) (δ := 173/20000000) (ψ := 106031/200000) 223 12
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t2 : ((748125959667/5000000000000 : ℚ) : ℝ) ≤ stT223o2 2 := by
  have hc : ((105801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((748125959667/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((105801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c3 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-424423/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log ((3 : ℕ)) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((3 : ℕ)) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1292297/2000000) (δ := 191/20000000) (ψ := 106031/200000) 223 19
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t3 : ((-4786233987/9765625000 : ℚ) : ℝ) ≤ stT223o2 3 := by
  have hc : ((-13264/15625 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4786233987/9765625000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-13264/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c4 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-248659/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log ((4 : ℕ)) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((4 : ℕ)) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7594917/10000000) (δ := 161/25000000) (ψ := 106031/200000) 223 25
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t4 : ((-2486715497343/5000000000000 : ℚ) : ℝ) ≤ stT223o2 4 := by
  have hc : ((-497343/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2486715497343/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-497343/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c5 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-494489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log ((5 : ℕ)) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((5 : ℕ)) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7482459/10000000) (δ := 981/100000000) (ψ := 106031/200000) 223 28
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t5 : ((-138220866369/312500000000 : ℚ) : ℝ) ≤ stT223o2 5 := by
  have hc : ((-247257/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138220866369/312500000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-247257/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c6 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-14863/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log ((6 : ℕ)) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((6 : ℕ)) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4527261/10000000) (δ := 367/50000000) (ψ := 106031/200000) 223 32
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t6 : ((-485525620707/5000000000000 : ℚ) : ℝ) ≤ stT223o2 6 := by
  have hc : ((-118929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-485525620707/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-118929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c7 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-29553/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log ((7 : ℕ)) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((7 : ℕ)) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1405263/2000000) (δ := 587/100000000) (ψ := 106031/200000) 223 34
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t7 : ((-357458414017/1000000000000 : ℚ) : ℝ) ≤ stT223o2 7 := by
  have hc : ((-472873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-357458414017/1000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-472873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c8 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((51029/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log ((8 : ℕ)) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((8 : ℕ)) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2875699/10000000) (δ := 133/20000000) (ψ := 106031/200000) 223 37
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t8 : ((721570465503/5000000000000 : ℚ) : ℝ) ≤ stT223o2 8 := by
  have hc : ((204091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((721570465503/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((204091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c9 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((834351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log ((9 : ℕ)) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((9 : ℕ)) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -291921/2000000) (δ := 33/4000000) (ψ := 106031/200000) 223 39
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t9 : ((2781003055233/10000000000000 : ℚ) : ℝ) ≤ stT223o2 9 := by
  have hc : ((834301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2781003055233/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((834301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c10 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((2617/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log ((10 : ℕ)) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((10 : ℕ)) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3506287/10000000) (δ := 1031/100000000) (ψ := 106031/200000) 223 41
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t10 : ((264742668163/5000000000000 : ℚ) : ℝ) ≤ stT223o2 10 := by
  have hc : ((83719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264742668163/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((83719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c11 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-39201/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log ((11 : ℕ)) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((11 : ℕ)) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3676731/5000000) (δ := 99/12500000) (ψ := 106031/200000) 223 42
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t11 : ((-59100757071/200000000000 : ℚ) : ℝ) ≤ stT223o2 11 := by
  have hc : ((-39203/40000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59100757071/200000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-39203/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c12 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((498527/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log ((12 : ℕ)) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((12 : ℕ)) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 191957/10000000) (δ := 23/4000000) (ψ := 106031/200000) 223 44
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t12 : ((719525573501/2500000000000 : ℚ) : ℝ) ≤ stT223o2 12 := by
  have hc : ((249251/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((719525573501/2500000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((249251/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c13 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-455883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log ((13 : ℕ)) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((13 : ℕ)) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3397949/5000000) (δ := 609/100000000) (ψ := 106031/200000) 223 45
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t13 : ((-316115323477/1250000000000 : ℚ) : ℝ) ≤ stT223o2 13 := by
  have hc : ((-113977/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-316115323477/1250000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-113977/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c14 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-443/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log ((14 : ℕ)) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((14 : ℕ)) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3962431/10000000) (δ := 101/12500000) (ψ := 106031/200000) 223 47
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t14 : ((-19010296269/5000000000000 : ℚ) : ℝ) ≤ stT223o2 14 := by
  have hc : ((-7113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19010296269/5000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-7113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c15 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((123081/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log ((15 : ℕ)) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((15 : ℕ)) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -438631/10000000) (δ := 139/12500000) (ψ := 106031/200000) 223 48
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t15 : ((317777527603/1250000000000 : ℚ) : ℝ) ≤ stT223o2 15 := by
  have hc : ((492299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((317777527603/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((492299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c16 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((370107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log ((16 : ℕ)) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((16 : ℕ)) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 921759/5000000) (δ := 7/781250) (ψ := 106031/200000) 223 49
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t16 : ((185041/1000000 : ℚ) : ℝ) ≤ stT223o2 16 := by
  have hc : ((185041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185041/1000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((185041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c17 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((349399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log ((17 : ℕ)) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((17 : ℕ)) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 758667/2500000) (δ := 41/6250000) (ψ := 106031/200000) 223 50
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t17 : ((211823923311/2500000000000 : ℚ) : ℝ) ≤ stT223o2 17 := by
  have hc : ((349349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211823923311/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((349349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c18 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((16487/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log ((18 : ℕ)) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((18 : ℕ)) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3259613/10000000) (δ := 633/100000000) (ψ := 106031/200000) 223 51
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t18 : ((155411424081/2500000000000 : ℚ) : ℝ) ≤ stT223o2 18 := by
  have hc : ((131871/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155411424081/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((131871/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c19 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((7786/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log ((19 : ℕ)) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((19 : ℕ)) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 327861/1250000) (δ := 221/25000000) (ψ := 106031/200000) 223 52
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t19 : ((571536450939/5000000000000 : ℚ) : ℝ) ≤ stT223o2 19 := by
  have hc : ((249127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((571536450939/5000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((249127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c20 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((176919/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log ((20 : ℕ)) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((20 : ℕ)) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 121293/1000000) (δ := 1/125000) (ψ := 106031/200000) 223 53
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t20 : ((395580376903/2000000000000 : ℚ) : ℝ) ≤ stT223o2 20 := by
  have hc : ((176909/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((395580376903/2000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((176909/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c21 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((936631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log ((21 : ℕ)) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((21 : ℕ)) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -35791/400000) (δ := 359/50000000) (ψ := 106031/200000) 223 54
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t21 : ((1021893226709/5000000000000 : ℚ) : ℝ) ≤ stT223o2 21 := by
  have hc : ((936581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1021893226709/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((936581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c22 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((58209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log ((22 : ℕ)) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((22 : ℕ)) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -908821/2500000) (δ := 571/100000000) (ψ := 106031/200000) 223 55
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t22 : ((15506086911/625000000000 : ℚ) : ℝ) ≤ stT223o2 22 := by
  have hc : ((7273/62500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15506086911/625000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((7273/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c23 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-467831/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log ((23 : ℕ)) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((23 : ℕ)) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3476159/5000000) (δ := 473/50000000) (ψ := 106031/200000) 223 56
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t23 : ((-12194344989/62500000000 : ℚ) : ℝ) ≤ stT223o2 23 := by
  have hc : ((-29241/31250 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12194344989/62500000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-29241/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c24 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-383583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log ((24 : ℕ)) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((24 : ℕ)) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2455587/5000000) (δ := 403/50000000) (ψ := 106031/200000) 223 56
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t24 : ((-391543896093/5000000000000 : ℚ) : ℝ) ≤ stT223o2 24 := by
  have hc : ((-383633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-391543896093/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-383633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c25 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((972993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log ((25 : ℕ)) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((25 : ℕ)) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 291171/5000000) (δ := 107/12500000) (ψ := 106031/200000) 223 57
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t25 : ((972943/5000000 : ℚ) : ℝ) ≤ stT223o2 25 := by
  have hc : ((972943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((972943/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((972943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c26 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-106143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log ((26 : ℕ)) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((26 : ℕ)) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -262053/625000) (δ := 73/10000000) (ψ := 106031/200000) 223 58
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t26 : ((-104130838133/5000000000000 : ℚ) : ℝ) ≤ stT223o2 26 := by
  have hc : ((-106193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104130838133/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-106193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c27 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-163851/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log ((27 : ℕ)) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((27 : ℕ)) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6327269/10000000) (δ := 723/100000000) (ψ := 106031/200000) 223 58
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t27 : ((-315350658361/2000000000000 : ℚ) : ℝ) ≤ stT223o2 27 := by
  have hc : ((-163861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-315350658361/2000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-163861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c28 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((954531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log ((28 : ℕ)) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((28 : ℕ)) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 378393/5000000) (δ := 1039/100000000) (ψ := 106031/200000) 223 59
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t28 : ((901899596191/5000000000000 : ℚ) : ℝ) ≤ stT223o2 28 := by
  have hc : ((954481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((901899596191/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((954481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c29 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-29799/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log ((29 : ℕ)) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((29 : ℕ)) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5169471/10000000) (δ := 783/100000000) (ψ := 106031/200000) 223 60
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t29 : ((-221364700909/2500000000000 : ℚ) : ℝ) ≤ stT223o2 29 := by
  have hc : ((-238417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221364700909/2500000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-238417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c30 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-140967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log ((30 : ℕ)) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((30 : ℕ)) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2140293/5000000) (δ := 89/10000000) (ψ := 106031/200000) 223 60
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t30 : ((-128730329807/5000000000000 : ℚ) : ℝ) ≤ stT223o2 30 := by
  have hc : ((-141017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128730329807/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-141017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c31 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((609881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log ((31 : ℕ)) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((31 : ℕ)) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1143607/5000000) (δ := 1083/100000000) (ψ := 106031/200000) 223 61
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t31 : ((1095288797043/10000000000000 : ℚ) : ℝ) ≤ stT223o2 31 := by
  have hc : ((609831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1095288797043/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((609831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c32 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-434777/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log ((32 : ℕ)) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((32 : ℕ)) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 410171/625000) (δ := 17/1562500) (ψ := 106031/200000) 223 61
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t32 : ((-384314313567/2500000000000 : ℚ) : ℝ) ≤ stT223o2 32 := by
  have hc : ((-217401/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-384314313567/2500000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-217401/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c33 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((487167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log ((33 : ℕ)) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((33 : ℕ)) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -141907/2500000) (δ := 661/100000000) (ψ := 106031/200000) 223 62
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t33 : ((53000318887/312500000000 : ℚ) : ℝ) ≤ stT223o2 33 := by
  have hc : ((243571/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53000318887/312500000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((243571/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c34 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-999199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log ((34 : ℕ)) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((34 : ℕ)) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3876943/5000000) (δ := 847/100000000) (ψ := 106031/200000) 223 62
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t34 : ((-856849022757/5000000000000 : ℚ) : ℝ) ≤ stT223o2 34 := by
  have hc : ((-999249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-856849022757/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-999249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c35 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((499363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log ((35 : ℕ)) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((35 : ℕ)) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 63099/5000000) (δ := 657/100000000) (ψ := 106031/200000) 223 63
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t35 : ((105504377013/625000000000 : ℚ) : ℝ) ≤ stT223o2 35 := by
  have hc : ((249669/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105504377013/625000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((249669/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c36 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-998753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log ((36 : ℕ)) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((36 : ℕ)) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7729133/10000000) (δ := 353/50000000) (ψ := 106031/200000) 223 64
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t36 : ((-1664671999601/10000000000000 : ℚ) : ℝ) ≤ stT223o2 36 := by
  have hc : ((-998803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1664671999601/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-998803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c37 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((31229/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log ((37 : ℕ)) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((37 : ℕ)) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -91669/10000000) (δ := 249/25000000) (ψ := 106031/200000) 223 64
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t37 : ((821401019971/5000000000000 : ℚ) : ℝ) ≤ stT223o2 37 := by
  have hc : ((499639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((821401019971/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((499639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c38 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-122389/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log ((38 : ℕ)) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((38 : ℕ)) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1468421/2000000) (δ := 163/25000000) (ψ := 106031/200000) 223 64
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t38 : ((-158841128383/1000000000000 : ℚ) : ℝ) ≤ stT223o2 38 := by
  have hc : ((-489581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158841128383/1000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-489581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c39 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((450207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log ((39 : ℕ)) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((39 : ℕ)) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -140649/1250000) (δ := 1/156250) (ψ := 106031/200000) 223 65
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t39 : ((360433941571/2500000000000 : ℚ) : ℝ) ≤ stT223o2 39 := by
  have hc : ((225091/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((360433941571/2500000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((225091/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c40 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-89849/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log ((40 : ℕ)) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((40 : ℕ)) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5932147/10000000) (δ := 71/12500000) (ψ := 106031/200000) 223 65
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t40 : ((-568294560519/5000000000000 : ℚ) : ℝ) ≤ stT223o2 40 := by
  have hc : ((-359421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-568294560519/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-359421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c41 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((401997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log ((41 : ℕ)) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((41 : ℕ)) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -11571/40000) (δ := 729/100000000) (ψ := 106031/200000) 223 66
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t41 : ((627735501939/10000000000000 : ℚ) : ℝ) ≤ stT223o2 41 := by
  have hc : ((401947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((627735501939/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((401947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c42 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((2563/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log ((42 : ℕ)) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((42 : ℕ)) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1912221/5000000) (δ := 949/100000000) (ψ := 106031/200000) 223 66
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t42 : ((31599772807/5000000000000 : ℚ) : ℝ) ≤ stT223o2 42 := by
  have hc : ((20479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31599772807/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((20479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c43 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-265153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log ((43 : ℕ)) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((43 : ℕ)) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1064879/2000000) (δ := 973/100000000) (ψ := 106031/200000) 223 67
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t43 : ((-101098184377/1250000000000 : ℚ) : ℝ) ≤ stT223o2 43 := by
  have hc : ((-132589/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101098184377/1250000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-132589/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c44 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((90747/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log ((44 : ℕ)) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((44 : ℕ)) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 541967/5000000) (δ := 369/50000000) (ψ := 106031/200000) 223 67
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t44 : ((17099830819/125000000000 : ℚ) : ℝ) ≤ stT223o2 44 := by
  have hc : ((45371/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17099830819/125000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((45371/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c45 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-122451/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log ((45 : ℕ)) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((45 : ℕ)) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3674121/5000000) (δ := 49/5000000) (ψ := 106031/200000) 223 67
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t45 : ((-91274246031/625000000000 : ℚ) : ℝ) ≤ stT223o2 45 := by
  have hc : ((-489829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91274246031/625000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-489829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c46 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((626891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log ((46 : ℕ)) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((46 : ℕ)) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2233101/10000000) (δ := 211/20000000) (ψ := 106031/200000) 223 68
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t46 : ((924226280379/10000000000000 : ℚ) : ℝ) ≤ stT223o2 46 := by
  have hc : ((626841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((924226280379/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((626841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c47 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((66047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log ((47 : ℕ)) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((47 : ℕ)) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1880877/5000000) (δ := 277/25000000) (ψ := 106031/200000) 223 68
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t47 : ((96266458053/10000000000000 : ℚ) : ℝ) ≤ stT223o2 47 := by
  have hc : ((65997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96266458053/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((65997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c48 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-378997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log ((48 : ℕ)) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((48 : ℕ)) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1519393/2500000) (δ := 1027/100000000) (ψ := 106031/200000) 223 69
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t48 : ((-17095976821/156250000000 : ℚ) : ℝ) ≤ stT223o2 48 := by
  have hc : ((-189511/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17095976821/156250000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-189511/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c49 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((123913/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log ((49 : ℕ)) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((49 : ℕ)) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -65989/2000000) (δ := 1091/100000000) (ψ := 106031/200000) 223 69
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t49 : ((708038359017/5000000000000 : ℚ) : ℝ) ≤ stT223o2 49 := by
  have hc : ((495627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((708038359017/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((495627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c50 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-26127/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log ((50 : ℕ)) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((50 : ℕ)) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5301559/10000000) (δ := 1087/100000000) (ψ := 106031/200000) 223 69
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t50 : ((-36952704713/500000000000 : ℚ) : ℝ) ≤ stT223o2 50 := by
  have hc : ((-52259/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36952704713/500000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-52259/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c51 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-374421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log ((51 : ℕ)) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((51 : ℕ)) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2443211/5000000) (δ := 393/50000000) (ψ := 106031/200000) 223 70
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t51 : ((-524364626351/10000000000000 : ℚ) : ℝ) ≤ stT223o2 51 := by
  have hc : ((-374471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-524364626351/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-374471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c52 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((977917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log ((52 : ℕ)) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((52 : ℕ)) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 52637/1000000) (δ := 921/100000000) (ψ := 106031/200000) 223 70
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t52 : ((5424228249/40000000000 : ℚ) : ℝ) ≤ stT223o2 52 := by
  have hc : ((977867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5424228249/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((977867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c53 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-138309/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log ((53 : ℕ)) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((53 : ℕ)) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2918027/5000000) (δ := 991/100000000) (ψ := 106031/200000) 223 70
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t53 : ((-94997904157/1000000000000 : ℚ) : ℝ) ≤ stT223o2 53 := by
  have hc : ((-138319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94997904157/1000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-138319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c54 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-144793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log ((54 : ℕ)) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((54 : ℕ)) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4661477/10000000) (δ := 77/12500000) (ψ := 106031/200000) 223 71
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t54 : ((-24634048663/625000000000 : ℚ) : ℝ) ≤ stT223o2 54 := by
  have hc : ((-72409/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24634048663/625000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-72409/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c55 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((983603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log ((55 : ℕ)) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((55 : ℕ)) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 90669/2000000) (δ := 917/100000000) (ψ := 106031/200000) 223 71
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t55 : ((1326221881647/10000000000000 : ℚ) : ℝ) ≤ stT223o2 55 := by
  have hc : ((983553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1326221881647/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((983553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c56 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-290357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log ((56 : ℕ)) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((56 : ℕ)) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1369001/2500000) (δ := 501/50000000) (ψ := 106031/200000) 223 71
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t56 : ((-194019749637/2500000000000 : ℚ) : ℝ) ≤ stT223o2 56 := by
  have hc : ((-145191/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194019749637/2500000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-145191/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c57 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-104279/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log ((57 : ℕ)) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((57 : ℕ)) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2649101/5000000) (δ := 753/100000000) (ψ := 106031/200000) 223 72
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t57 : ((-138134222037/2000000000000 : ℚ) : ℝ) ≤ stT223o2 57 := by
  have hc : ((-104289/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138134222037/2000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-104289/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c58 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((39353/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log ((58 : ℕ)) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((58 : ℕ)) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -225127/5000000) (δ := 203/20000000) (ψ := 106031/200000) 223 72
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t58 : ((6458797683/50000000000 : ℚ) : ℝ) ≤ stT223o2 58 := by
  have hc : ((39351/40000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6458797683/50000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((39351/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c59 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-15451/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log ((59 : ℕ)) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((59 : ℕ)) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4314819/10000000) (δ := 131/20000000) (ψ := 106031/200000) 223 72
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t59 : ((-62881287/3125000000 : ℚ) : ℝ) ≤ stT223o2 59 := by
  have hc : ((-483/3125 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62881287/3125000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-483/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c60 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-896793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log ((60 : ℕ)) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((60 : ℕ)) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -20963/31250) (δ := 669/100000000) (ψ := 106031/200000) 223 73
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t60 : ((-231563965757/2000000000000 : ℚ) : ℝ) ≤ stT223o2 60 := by
  have hc : ((-896843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-231563965757/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-896843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c61 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((667279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log ((61 : ℕ)) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((61 : ℕ)) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2100617/10000000) (δ := 347/50000000) (ψ := 106031/200000) 223 73
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t61 : ((53393666267/625000000000 : ℚ) : ℝ) ≤ stT223o2 61 := by
  have hc : ((667229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53393666267/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((667229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c62 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((562987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log ((62 : ℕ)) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((62 : ℕ)) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2432003/10000000) (δ := 919/100000000) (ψ := 106031/200000) 223 73
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t62 : ((714930552937/10000000000000 : ℚ) : ℝ) ≤ stT223o2 62 := by
  have hc : ((562937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((714930552937/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((562937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c63 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-926891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log ((63 : ℕ)) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((63 : ℕ)) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3446049/5000000) (δ := 859/100000000) (ψ := 106031/200000) 223 73
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t63 : ((-583918140481/5000000000000 : ℚ) : ℝ) ≤ stT223o2 63 := by
  have hc : ((-926941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-583918140481/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-926941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c64 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-39657/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log ((64 : ℕ)) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((64 : ℕ)) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -442601/1000000) (δ := 37/4000000) (ψ := 106031/200000) 223 74
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t64 : ((-49583789667/2000000000000 : ℚ) : ℝ) ≤ stT223o2 64 := by
  have hc : ((-39667/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49583789667/2000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-39667/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c65 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((999131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log ((65 : ℕ)) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((65 : ℕ)) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -52109/5000000) (δ := 31/4000000) (ψ := 106031/200000) 223 74
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t65 : ((1239207121107/10000000000000 : ℚ) : ℝ) ≤ stT223o2 65 := by
  have hc : ((999081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1239207121107/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((999081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c66 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-89719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log ((66 : ℕ)) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((66 : ℕ)) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 415159/1000000) (δ := 81/12500000) (ψ := 106031/200000) 223 74
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t66 : ((-22099601727/2000000000000 : ℚ) : ℝ) ≤ stT223o2 66 := by
  have hc : ((-89769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22099601727/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-89769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c67 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-980899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log ((67 : ℕ)) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((67 : ℕ)) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1472913/2000000) (δ := 903/100000000) (ψ := 106031/200000) 223 75
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t67 : ((-239684097711/2000000000000 : ℚ) : ℝ) ≤ stT223o2 67 := by
  have hc : ((-980949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239684097711/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-980949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c68 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((273329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log ((68 : ℕ)) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((68 : ℕ)) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -161743/500000) (δ := 267/25000000) (ψ := 106031/200000) 223 75
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t68 : ((165699715581/5000000000000 : ℚ) : ℝ) ≤ stT223o2 68 := by
  have hc : ((273279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165699715581/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((273279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c69 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((944797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log ((69 : ℕ)) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((69 : ℕ)) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 166911/2000000) (δ := 17/1562500) (ψ := 106031/200000) 223 75
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t69 : ((568670616963/5000000000000 : ℚ) : ℝ) ≤ stT223o2 69 := by
  have hc : ((944747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((568670616963/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((944747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c70 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-179581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log ((70 : ℕ)) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((70 : ℕ)) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 605677/1250000) (δ := 653/100000000) (ψ := 106031/200000) 223 75
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t70 : ((-107335149887/2500000000000 : ℚ) : ℝ) ≤ stT223o2 70 := by
  have hc : ((-89803/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107335149887/2500000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-89803/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c71 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-185869/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log ((71 : ℕ)) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((71 : ℕ)) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6908581/10000000) (δ := 413/50000000) (ψ := 106031/200000) 223 76
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t71 : ((-110298925689/1000000000000 : ℚ) : ℝ) ≤ stT223o2 71 := by
  have hc : ((-185879/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110298925689/1000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-185879/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c72 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((179329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log ((72 : ℕ)) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((72 : ℕ)) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -752479/2500000) (δ := 937/100000000) (ψ := 106031/200000) 223 76
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t72 : ((26413967043/625000000000 : ℚ) : ℝ) ≤ stT223o2 72 := by
  have hc : ((22413/62500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26413967043/625000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((22413/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c73 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((472371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log ((73 : ℕ)) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((73 : ℕ)) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 834973/10000000) (δ := 21/3125000) (ψ := 106031/200000) 223 76
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t73 : ((276419477103/2500000000000 : ℚ) : ℝ) ≤ stT223o2 73 := by
  have hc : ((236173/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((276419477103/2500000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((236173/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c74 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-27657/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log ((74 : ℕ)) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((74 : ℕ)) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1156887/2500000) (δ := 503/50000000) (ψ := 106031/200000) 223 76
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t74 : ((-16078219387/500000000000 : ℚ) : ℝ) ≤ stT223o2 74 := by
  have hc : ((-13831/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16078219387/500000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-13831/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c75 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-489419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log ((75 : ℕ)) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((75 : ℕ)) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1834687/2500000) (δ := 493/50000000) (ψ := 106031/200000) 223 77
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t75 : ((-141290369061/1250000000000 : ℚ) : ℝ) ≤ stT223o2 75 := by
  have hc : ((-122361/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141290369061/1250000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-122361/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c76 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((22381/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log ((76 : ℕ)) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((76 : ℕ)) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3646641/10000000) (δ := 343/50000000) (ψ := 106031/200000) 223 77
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t76 : ((12830640969/1000000000000 : ℚ) : ℝ) ≤ stT223o2 76 := by
  have hc : ((22371/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12830640969/1000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((22371/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c77 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log ((77 : ℕ)) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((77 : ℕ)) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1399/5000000) (δ := 881/100000000) (ψ := 106031/200000) 223 77
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t77 : ((227909376029/2000000000000 : ℚ) : ℝ) ≤ stT223o2 77 := by
  have hc : ((999949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227909376029/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((999949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c78 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((132793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log ((78 : ℕ)) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((78 : ℕ)) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1797013/5000000) (δ := 831/100000000) (ψ := 106031/200000) 223 77
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t78 : ((150301845811/10000000000000 : ℚ) : ℝ) ≤ stT223o2 78 := by
  have hc : ((132743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150301845811/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((132743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c79 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-48003/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log ((79 : ℕ)) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((79 : ℕ)) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7145029/10000000) (δ := 561/100000000) (ψ := 106031/200000) 223 77
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t79 : ((-3375650749/31250000000 : ℚ) : ℝ) ≤ stT223o2 79 := by
  have hc : ((-96011/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3375650749/31250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-96011/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c80 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-27289/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log ((80 : ℕ)) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((80 : ℕ)) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2528299/5000000) (δ := 73/10000000) (ψ := 106031/200000) 223 78
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t80 : ((-122054094729/2500000000000 : ℚ) : ℝ) ≤ stT223o2 80 := by
  have hc : ((-218337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122054094729/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-218337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c81 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((803569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log ((81 : ℕ)) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((81 : ℕ)) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1593821/10000000) (δ := 593/100000000) (ψ := 106031/200000) 223 78
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t81 : ((892798799609/10000000000000 : ℚ) : ℝ) ≤ stT223o2 81 := by
  have hc : ((803519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((892798799609/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((803519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c82 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((744783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log ((82 : ℕ)) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((82 : ℕ)) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1826467/10000000) (δ := 31/5000000) (ψ := 106031/200000) 223 78
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t82 : ((164483964579/2000000000000 : ℚ) : ℝ) ≤ stT223o2 82 := by
  have hc : ((744733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164483964579/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((744733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c83 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-489331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log ((83 : ℕ)) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((83 : ℕ)) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5205297/10000000) (δ := 103/10000000) (ψ := 106031/200000) 223 78
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t83 : ((-537165628983/10000000000000 : ℚ) : ℝ) ≤ stT223o2 83 := by
  have hc : ((-489381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-537165628983/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-489381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c84 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-240547/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log ((84 : ℕ)) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((84 : ℕ)) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7164303/10000000) (δ := 113/10000000) (ψ := 106031/200000) 223 79
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t84 : ((-52494412971/500000000000 : ℚ) : ℝ) ≤ stT223o2 84 := by
  have hc : ((-481119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52494412971/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-481119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c85 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((4923/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log ((85 : ℕ)) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((85 : ℕ)) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -483181/1250000) (δ := 157/25000000) (ψ := 106031/200000) 223 79
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t85 : ((1332223819/500000000000 : ℚ) : ℝ) ≤ stT223o2 85 := by
  have hc : ((4913/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1332223819/500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((4913/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c86 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((242711/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log ((86 : ℕ)) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((86 : ℕ)) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -605177/10000000) (δ := 267/25000000) (ψ := 106031/200000) 223 79
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t86 : ((523416690819/5000000000000 : ℚ) : ℝ) ≤ stT223o2 86 := by
  have hc : ((485397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((523416690819/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((485397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c87 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((100041/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log ((87 : ℕ)) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((87 : ℕ)) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1308701/5000000) (δ := 37/4000000) (ψ := 106031/200000) 223 79
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t87 : ((6702777217/125000000000 : ℚ) : ℝ) ≤ stT223o2 87 := by
  have hc : ((100031/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6702777217/125000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((100031/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c88 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-340989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log ((88 : ℕ)) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((88 : ℕ)) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5803151/10000000) (δ := 97/10000000) (ψ := 106031/200000) 223 79
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t88 : ((-45440286007/625000000000 : ℚ) : ℝ) ≤ stT223o2 88 := by
  have hc : ((-170507/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45440286007/625000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-170507/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c89 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-180987/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log ((89 : ℕ)) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((89 : ℕ)) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6755061/10000000) (δ := 387/50000000) (ψ := 106031/200000) 223 80
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t89 : ((-95928229003/1000000000000 : ℚ) : ℝ) ≤ stT223o2 89 := by
  have hc : ((-180997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95928229003/1000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-180997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c90 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((14293/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log ((90 : ℕ)) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((90 : ℕ)) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -455063/1250000) (δ := 759/100000000) (ψ := 106031/200000) 223 80
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t90 : ((15059548881/1250000000000 : ℚ) : ℝ) ≤ stT223o2 90 := by
  have hc : ((57147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15059548881/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((57147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c91 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((194997/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log ((91 : ℕ)) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((91 : ℕ)) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -280181/5000000) (δ := 1169/100000000) (ψ := 106031/200000) 223 80
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t91 : ((51100438077/500000000000 : ℚ) : ℝ) ≤ stT223o2 91 := by
  have hc : ((194987/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51100438077/500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((194987/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c92 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((544967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log ((92 : ℕ)) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((92 : ℕ)) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 621529/2500000) (δ := 103/12500000) (ψ := 106031/200000) 223 80
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t92 : ((142028801631/2500000000000 : ℚ) : ℝ) ≤ stT223o2 92 := by
  have hc : ((544917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142028801631/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((544917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c93 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-588391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log ((93 : ℕ)) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((93 : ℕ)) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5499659/10000000) (δ := 1009/100000000) (ψ := 106031/200000) 223 80
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t93 : ((-76273133979/1250000000000 : ℚ) : ℝ) ≤ stT223o2 93 := by
  have hc : ((-588441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76273133979/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-588441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c94 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-193743/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log ((94 : ℕ)) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((94 : ℕ)) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -451687/625000) (δ := 181/20000000) (ψ := 106031/200000) 223 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t94 : ((-99920553383/1000000000000 : ℚ) : ℝ) ≤ stT223o2 94 := by
  have hc : ((-193753/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99920553383/1000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-193753/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c95 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-139637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log ((95 : ℕ)) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((95 : ℕ)) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4277229/10000000) (δ := 101/10000000) (ψ := 106031/200000) 223 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t95 : ((-143315928573/10000000000000 : ℚ) : ℝ) ≤ stT223o2 95 := by
  have hc : ((-139687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143315928573/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-139687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c96 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((427993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log ((96 : ℕ)) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((96 : ℕ)) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -679177/5000000) (δ := 203/20000000) (ψ := 106031/200000) 223 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t96 : ((341244297/3906250000 : ℚ) : ℝ) ≤ stT223o2 96 := by
  have hc : ((13374/15625 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((341244297/3906250000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((13374/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c97 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((409219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log ((97 : ℕ)) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((97 : ℕ)) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1530273/10000000) (δ := 7/800000) (ψ := 106031/200000) 223 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t97 : ((103868372781/1250000000000 : ℚ) : ℝ) ≤ stT223o2 97 := by
  have hc : ((204597/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103868372781/1250000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((204597/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c98 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-9193/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log ((98 : ℕ)) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((98 : ℕ)) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 548659/1250000) (δ := 43/5000000) (ψ := 106031/200000) 223 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t98 : ((-18577723823/1000000000000 : ℚ) : ℝ) ≤ stT223o2 98 := by
  have hc : ((-18391/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18577723823/1000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-18391/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c99 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-483971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log ((99 : ℕ)) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((99 : ℕ)) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3609623/5000000) (δ := 7/1250000) (ψ := 106031/200000) 223 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t99 : ((-60804296481/625000000000 : ℚ) : ℝ) ≤ stT223o2 99 := by
  have hc : ((-120999/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60804296481/625000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-120999/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c100 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-161833/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log ((100 : ℕ)) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((100 : ℕ)) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5687187/10000000) (δ := 37/4000000) (ψ := 106031/200000) 223 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t100 : ((-323691/5000000 : ℚ) : ℝ) ≤ stT223o2 100 := by
  have hc : ((-323691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-323691/5000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-323691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c101 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((394371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log ((101 : ℕ)) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((101 : ℕ)) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -728383/2500000) (δ := 953/100000000) (ψ := 106031/200000) 223 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t101 : ((392363984877/10000000000000 : ℚ) : ℝ) ≤ stT223o2 101 := by
  have hc : ((394321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((392363984877/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((394321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c102 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((249441/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log ((102 : ℕ)) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((102 : ℕ)) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -41801/2500000) (δ := 489/50000000) (ψ := 106031/200000) 223 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t102 : ((493941761979/5000000000000 : ℚ) : ℝ) ≤ stT223o2 102 := by
  have hc : ((498857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((493941761979/5000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((498857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c103 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((130643/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log ((103 : ℕ)) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((103 : ℕ)) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2552329/10000000) (δ := 189/20000000) (ψ := 106031/200000) 223 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t103 : ((257428039869/5000000000000 : ℚ) : ℝ) ≤ stT223o2 103 := by
  have hc : ((261261/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((257428039869/5000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((261261/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c104 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-251661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log ((104 : ℕ)) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((104 : ℕ)) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5245587/10000000) (δ := 27/2500000) (ψ := 106031/200000) 223 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t104 : ((-123399254783/2500000000000 : ℚ) : ℝ) ≤ stT223o2 104 := by
  have hc : ((-125843/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123399254783/2500000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-125843/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c105 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-999721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log ((105 : ℕ)) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((105 : ℕ)) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1948723/2500000) (δ := 37/6250000) (ψ := 106031/200000) 223 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t105 : ((-975677518671/10000000000000 : ℚ) : ℝ) ≤ stT223o2 105 := by
  have hc : ((-999771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-975677518671/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-999771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c106 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-470873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log ((106 : ℕ)) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((106 : ℕ)) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1288173/2500000) (δ := 1021/100000000) (ψ := 106031/200000) 223 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t106 : ((-228700458489/5000000000000 : ℚ) : ℝ) ≤ stT223o2 106 := by
  have hc : ((-470923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228700458489/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-470923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c107 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((528367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log ((107 : ℕ)) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((107 : ℕ)) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1267651/5000000) (δ := 767/100000000) (ψ := 106031/200000) 223 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t107 : ((31921441457/625000000000 : ℚ) : ℝ) ≤ stT223o2 107 := by
  have hc : ((528317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31921441457/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((528317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c108 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((999733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log ((108 : ℕ)) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((108 : ℕ)) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2887/500000) (δ := 847/100000000) (ψ := 106031/200000) 223 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t108 : ((3847779867/40000000000 : ℚ) : ℝ) ≤ stT223o2 108 := by
  have hc : ((999683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3847779867/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((999683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c109 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((248459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log ((109 : ℕ)) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((109 : ℕ)) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2626883/10000000) (δ := 901/100000000) (ψ := 106031/200000) 223 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t109 : ((59489136121/1250000000000 : ℚ) : ℝ) ≤ stT223o2 109 := by
  have hc : ((124217/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59489136121/1250000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((124217/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c110 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-47787/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log ((110 : ℕ)) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((110 : ℕ)) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5172563/10000000) (δ := 363/50000000) (ψ := 106031/200000) 223 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t110 : ((-2847993981/62500000000 : ℚ) : ℝ) ≤ stT223o2 110 := by
  have hc : ((-2987/6250 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2847993981/62500000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-2987/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c111 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-31187/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log ((111 : ℕ)) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((111 : ℕ)) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1923801/2500000) (δ := 1137/100000000) (ψ := 106031/200000) 223 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t111 : ((-236822988843/2500000000000 : ℚ) : ℝ) ≤ stT223o2 111 := by
  have hc : ((-499017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236822988843/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-499017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c112 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-296307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log ((112 : ℕ)) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((112 : ℕ)) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2756371/5000000) (δ := 391/50000000) (ψ := 106031/200000) 223 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t112 : ((-4375119731/78125000000 : ℚ) : ℝ) ≤ stT223o2 112 := by
  have hc : ((-74083/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4375119731/78125000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-74083/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c113 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((174647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log ((113 : ℕ)) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((113 : ℕ)) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -758737/2500000) (δ := 463/50000000) (ψ := 106031/200000) 223 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t113 : ((1026690049/31250000000 : ℚ) : ℝ) ≤ stT223o2 113 := by
  have hc : ((87311/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1026690049/31250000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((87311/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c114 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((486651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log ((114 : ℕ)) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((114 : ℕ)) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -115797/2000000) (δ := 149/25000000) (ψ := 106031/200000) 223 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t114 : ((45576661221/500000000000 : ℚ) : ℝ) ≤ stT223o2 114 := by
  have hc : ((243313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45576661221/500000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((243313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c115 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((46061/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log ((115 : ℕ)) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((115 : ℕ)) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 231941/1250000) (δ := 831/100000000) (ψ := 106031/200000) 223 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t115 : ((42949152669/625000000000 : ℚ) : ℝ) ≤ stT223o2 115 := by
  have hc : ((368463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42949152669/625000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((368463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c116 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-136363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log ((116 : ℕ)) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((116 : ℕ)) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4268963/10000000) (δ := 987/100000000) (ψ := 106031/200000) 223 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t116 : ((-126656333001/10000000000000 : ℚ) : ℝ) ≤ stT223o2 116 := by
  have hc : ((-136413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126656333001/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-136413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c117 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-888413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log ((117 : ℕ)) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((117 : ℕ)) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3330841/5000000) (δ := 741/100000000) (ψ := 106031/200000) 223 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t117 : ((-821384931963/10000000000000 : ℚ) : ℝ) ≤ stT223o2 117 := by
  have hc : ((-888463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-821384931963/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-888463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c118 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-890651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log ((118 : ℕ)) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((118 : ℕ)) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6673927/10000000) (δ := 7/800000) (ψ := 106031/200000) 223 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t118 : ((-32798282923/400000000000 : ℚ) : ℝ) ≤ stT223o2 118 := by
  have hc : ((-890701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32798282923/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-890701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c119 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-78593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log ((119 : ℕ)) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((119 : ℕ)) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -540199/1250000) (δ := 1023/100000000) (ψ := 106031/200000) 223 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t119 : ((-36034520991/2500000000000 : ℚ) : ℝ) ≤ stT223o2 119 := by
  have hc : ((-39309/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36034520991/2500000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-39309/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c120 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((699873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log ((120 : ℕ)) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((120 : ℕ)) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -994471/5000000) (δ := 1/156250) (ψ := 106031/200000) 223 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t120 : ((63884742201/1000000000000 : ℚ) : ℝ) ≤ stT223o2 120 := by
  have hc : ((699823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63884742201/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((699823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c121 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((247899/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log ((121 : ℕ)) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((121 : ℕ)) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 324349/10000000) (δ := 31/5000000) (ψ := 106031/200000) 223 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t121 : ((45070227657/500000000000 : ℚ) : ℝ) ≤ stT223o2 121 := by
  have hc : ((495773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45070227657/500000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((495773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c122 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((49979/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log ((122 : ℕ)) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((122 : ℕ)) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 13093/50000) (δ := 131/20000000) (ψ := 106031/200000) 223 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t122 : ((22622155359/500000000000 : ℚ) : ℝ) ≤ stT223o2 122 := by
  have hc : ((24987/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22622155359/500000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((24987/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c123 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-94319/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log ((123 : ℕ)) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((123 : ℕ)) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4894123/10000000) (δ := 147/25000000) (ψ := 106031/200000) 223 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t123 : ((-17011176721/500000000000 : ℚ) : ℝ) ≤ stT223o2 123 := by
  have hc : ((-188663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17011176721/500000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-188663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c124 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-3843/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log ((124 : ℕ)) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((124 : ℕ)) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7151221/10000000) (δ := 91/12500000) (ψ := 106031/200000) 223 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t124 : ((-1078530427/12500000000 : ℚ) : ℝ) ≤ stT223o2 124 := by
  have hc : ((-1201/1250 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1078530427/12500000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-1201/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c125 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-51067/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log ((125 : ℕ)) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((125 : ℕ)) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -252711/400000) (δ := 73/10000000) (ψ := 106031/200000) 223 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t125 : ((-91357099527/1250000000000 : ℚ) : ℝ) ≤ stT223o2 125 := by
  have hc : ((-408561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91357099527/1250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-408561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c126 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-6781/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log ((126 : ℕ)) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((126 : ℕ)) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4096647/10000000) (δ := 13/1250000) (ψ := 106031/200000) 223 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t126 : ((-3022725303/500000000000 : ℚ) : ℝ) ≤ stT223o2 126 := by
  have hc : ((-3393/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3022725303/500000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-3393/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c127 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((36337/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log ((127 : ℕ)) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((127 : ℕ)) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1893079/10000000) (δ := 933/100000000) (ψ := 106031/200000) 223 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t127 : ((16120818291/250000000000 : ℚ) : ℝ) ≤ stT223o2 127 := by
  have hc : ((72669/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16120818291/250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((72669/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c128 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((99313/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log ((128 : ℕ)) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((128 : ℕ)) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 293207/10000000) (δ := 693/100000000) (ψ := 106031/200000) 223 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t128 : ((21944163241/250000000000 : ℚ) : ℝ) ≤ stT223o2 128 := by
  have hc : ((24827/25000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21944163241/250000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((24827/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c129 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((55287/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log ((129 : ℕ)) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((129 : ℕ)) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2462479/10000000) (δ := 43/4000000) (ψ := 106031/200000) 223 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t129 : ((486730369/10000000000 : ℚ) : ℝ) ≤ stT223o2 129 := by
  have hc : ((27641/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((486730369/10000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((27641/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c130 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-271743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log ((130 : ℕ)) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((130 : ℕ)) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4614999/10000000) (δ := 23/4000000) (ψ := 106031/200000) 223 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t130 : ((-238378496787/10000000000000 : ℚ) : ℝ) ≤ stT223o2 130 := by
  have hc : ((-271793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238378496787/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-271793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c131 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-904247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log ((131 : ℕ)) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((131 : ℕ)) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 270041/400000) (δ := 87/10000000) (ψ := 106031/200000) 223 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t131 : ((-158017762077/2000000000000 : ℚ) : ℝ) ≤ stT223o2 131 := by
  have hc : ((-904297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158017762077/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-904297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c132 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-918419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log ((132 : ℕ)) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((132 : ℕ)) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1709289/2500000) (δ := 869/100000000) (ψ := 106031/200000) 223 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t132 : ((-799425314441/10000000000000 : ℚ) : ℝ) ≤ stT223o2 132 := by
  have hc : ((-918469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-799425314441/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-918469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c133 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-316989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log ((133 : ℕ)) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((133 : ℕ)) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4733373/10000000) (δ := 829/100000000) (ψ := 106031/200000) 223 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t133 : ((-27490768729/1000000000000 : ℚ) : ℝ) ≤ stT223o2 133 := by
  have hc : ((-317039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27490768729/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-317039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c134 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((98099/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log ((134 : ℕ)) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((134 : ℕ)) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -661337/2500000) (δ := 567/50000000) (ψ := 106031/200000) 223 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t134 : ((21183987063/500000000000 : ℚ) : ℝ) ≤ stT223o2 134 := by
  have hc : ((98089/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21183987063/500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((98089/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c135 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((486931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log ((135 : ℕ)) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((135 : ℕ)) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -35803/625000) (δ := 849/100000000) (ψ := 106031/200000) 223 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t135 : ((104765372943/1250000000000 : ℚ) : ℝ) ≤ stT223o2 135 := by
  have hc : ((243453/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104765372943/1250000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((243453/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c136 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((828853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log ((136 : ℕ)) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((136 : ℕ)) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1484357/10000000) (δ := 467/50000000) (ψ := 106031/200000) 223 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t136 : ((177672985519/2500000000000 : ℚ) : ℝ) ≤ stT223o2 136 := by
  have hc : ((828803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177672985519/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((828803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c137 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((39879/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log ((137 : ℕ)) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((137 : ℕ)) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3526491/10000000) (δ := 839/100000000) (ψ := 106031/200000) 223 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t137 : ((68120446681/5000000000000 : ℚ) : ℝ) ≤ stT223o2 137 := by
  have hc : ((79733/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68120446681/5000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((79733/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c138 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-605753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log ((138 : ℕ)) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((138 : ℕ)) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1388443/2500000) (δ := 457/50000000) (ψ := 106031/200000) 223 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t138 : ((-515694044371/10000000000000 : ℚ) : ℝ) ≤ stT223o2 138 := by
  have hc : ((-605803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-515694044371/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-605803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c139 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-62087/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log ((139 : ℕ)) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((139 : ℕ)) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7566417/10000000) (δ := 749/100000000) (ψ := 106031/200000) 223 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t139 : ((-421313288269/5000000000000 : ℚ) : ℝ) ≤ stT223o2 139 := by
  have hc : ((-496721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-421313288269/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-496721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c140 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-774887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log ((140 : ℕ)) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((140 : ℕ)) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -614333/1000000) (δ := 873/100000000) (ψ := 106031/200000) 223 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t140 : ((-130988376047/2000000000000 : ℚ) : ℝ) ≤ stT223o2 140 := by
  have hc : ((-774937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130988376047/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-774937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c141 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-23201/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log ((141 : ℕ)) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((141 : ℕ)) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -519917/1250000) (δ := 199/20000000) (ψ := 106031/200000) 223 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t141 : ((-4887323863/625000000000 : ℚ) : ℝ) ≤ stT223o2 141 := by
  have hc : ((-46427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4887323863/625000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-46427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c142 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((25617/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log ((142 : ℕ)) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((142 : ℕ)) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2189363/10000000) (δ := 127/20000000) (ψ := 106031/200000) 223 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t142 : ((4299124263/80000000000 : ℚ) : ℝ) ≤ stT223o2 142 := by
  have hc : ((5123/8000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4299124263/80000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((5123/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c143 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((248913/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log ((143 : ℕ)) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((143 : ℕ)) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -46643/2000000) (δ := 803/100000000) (ψ := 106031/200000) 223 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t143 : ((208141051921/2500000000000 : ℚ) : ℝ) ≤ stT223o2 143 := by
  have hc : ((497801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208141051921/2500000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((497801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c144 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((193807/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log ((144 : ℕ)) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((144 : ℕ)) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 854651/5000000) (δ := 221/20000000) (ψ := 106031/200000) 223 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t144 : ((322990704137/5000000000000 : ℚ) : ℝ) ≤ stT223o2 144 := by
  have hc : ((387589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322990704137/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((387589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c145 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((11519/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log ((145 : ℕ)) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((145 : ℕ)) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 29107/80000) (δ := 167/25000000) (ψ := 106031/200000) 223 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t145 : ((2390461839/250000000000 : ℚ) : ℝ) ≤ stT223o2 145 := by
  have hc : ((5757/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2390461839/250000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((5757/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c146 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-302943/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log ((146 : ℕ)) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((146 : ℕ)) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 555419/1000000) (δ := 903/100000000) (ψ := 106031/200000) 223 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t146 : ((-15671133413/312500000000 : ℚ) : ℝ) ≤ stT223o2 146 := by
  have hc : ((-37871/62500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15671133413/312500000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-37871/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c147 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-493707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log ((147 : ℕ)) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((147 : ℕ)) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 233029/312500) (δ := 19/2000000) (ψ := 106031/200000) 223 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t147 : ((-101805933771/1250000000000 : ℚ) : ℝ) ≤ stT223o2 147 := by
  have hc : ((-123433/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101805933771/1250000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-123433/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c148 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-413481/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log ((148 : ℕ)) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((148 : ℕ)) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3180599/5000000) (δ := 157/20000000) (ψ := 106031/200000) 223 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t148 : ((-33989986447/500000000000 : ℚ) : ℝ) ≤ stT223o2 148 := by
  have hc : ((-206753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33989986447/500000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-206753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c149 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-110499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log ((149 : ℕ)) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((149 : ℕ)) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2242043/5000000) (δ := 267/25000000) (ψ := 106031/200000) 223 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t149 : ((-707381231/39062500000 : ℚ) : ℝ) ≤ stT223o2 149 := by
  have hc : ((-27631/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-707381231/39062500000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-27631/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c150 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((499467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log ((150 : ℕ)) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((150 : ℕ)) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2619531/10000000) (δ := 203/20000000) (ψ := 106031/200000) 223 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t150 : ((25485748927/625000000000 : ℚ) : ℝ) ≤ stT223o2 150 := by
  have hc : ((499417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25485748927/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((499417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c151 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((953261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log ((151 : ℕ)) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((151 : ℕ)) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -191841/2500000) (δ := 713/100000000) (ψ := 106031/200000) 223 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t151 : ((193927918317/2500000000000 : ℚ) : ℝ) ≤ stT223o2 151 := by
  have hc : ((953211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193927918317/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((953211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c152 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((90937/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log ((152 : ℕ)) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((152 : ℕ)) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 16759/156250) (δ := 459/50000000) (ψ := 106031/200000) 223 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t152 : ((18438895431/250000000000 : ℚ) : ℝ) ≤ stT223o2 152 := by
  have hc : ((22733/25000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18438895431/250000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((22733/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c153 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((199587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log ((153 : ℕ)) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((153 : ℕ)) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 725113/2500000) (δ := 111/12500000) (ψ := 106031/200000) 223 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t153 : ((20167037253/625000000000 : ℚ) : ℝ) ≤ stT223o2 153 := by
  have hc : ((99781/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20167037253/625000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((99781/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c154 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-6211/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log ((154 : ℕ)) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((154 : ℕ)) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4716419/10000000) (δ := 1113/100000000) (ψ := 106031/200000) 223 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t154 : ((-1251443119/50000000000 : ℚ) : ℝ) ≤ stT223o2 154 := by
  have hc : ((-1553/5000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1251443119/50000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-1553/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c155 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-430557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log ((155 : ℕ)) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((155 : ℕ)) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 815079/1250000) (δ := 121/12500000) (ψ := 106031/200000) 223 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t155 : ((-8646301851/125000000000 : ℚ) : ℝ) ≤ stT223o2 155 := by
  have hc : ((-215291/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8646301851/125000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-215291/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c156 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-491587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log ((156 : ℕ)) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((156 : ℕ)) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -46217/62500) (δ := 263/25000000) (ψ := 106031/200000) 223 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t156 : ((-98401180823/1250000000000 : ℚ) : ℝ) ≤ stT223o2 156 := by
  have hc : ((-122903/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98401180823/1250000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-122903/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c157 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-19519/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log ((157 : ℕ)) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((157 : ℕ)) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1403391/2500000) (δ := 541/50000000) (ψ := 106031/200000) 223 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t157 : ((-249265714623/5000000000000 : ℚ) : ℝ) ≤ stT223o2 157 := by
  have hc : ((-312329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249265714623/5000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-312329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c158 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((33303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log ((158 : ℕ)) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((158 : ℕ)) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3843717/10000000) (δ := 391/50000000) (ψ := 106031/200000) 223 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t158 : ((26454656921/10000000000000 : ℚ) : ℝ) ≤ stT223o2 158 := by
  have hc : ((33253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26454656921/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((33253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c159 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((167977/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log ((159 : ℕ)) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((159 : ℕ)) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -521259/2500000) (δ := 561/50000000) (ψ := 106031/200000) 223 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t159 : ((266408829379/5000000000000 : ℚ) : ℝ) ≤ stT223o2 159 := by
  have hc : ((335929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((266408829379/5000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((335929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c160 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((247727/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log ((160 : ℕ)) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((160 : ℕ)) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -337381/10000000) (δ := 481/50000000) (ψ := 106031/200000) 223 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t160 : ((391670809101/5000000000000 : ℚ) : ℝ) ≤ stT223o2 160 := by
  have hc : ((495429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391670809101/5000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((495429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c161 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((423693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log ((161 : ℕ)) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((161 : ℕ)) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 279877/2000000) (δ := 721/100000000) (ψ := 106031/200000) 223 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t161 : ((8347424687/125000000000 : ℚ) : ℝ) ≤ stT223o2 161 := by
  have hc : ((105917/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8347424687/125000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((105917/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c162 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((78793/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log ((162 : ℕ)) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((162 : ℕ)) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 781349/2500000) (δ := 757/100000000) (ψ := 106031/200000) 223 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t162 : ((61895790557/2500000000000 : ℚ) : ℝ) ≤ stT223o2 162 := by
  have hc : ((157561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61895790557/2500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((157561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c163 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-357433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log ((163 : ℕ)) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((163 : ℕ)) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2420393/5000000) (δ := 571/50000000) (ψ := 106031/200000) 223 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t163 : ((-280002492063/10000000000000 : ℚ) : ℝ) ≤ stT223o2 163 := by
  have hc : ((-357483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-280002492063/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-357483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c164 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-173233/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log ((164 : ℕ)) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((164 : ℕ)) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1309137/2000000) (δ := 203/25000000) (ψ := 106031/200000) 223 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t164 : ((-135280088167/2000000000000 : ℚ) : ℝ) ≤ stT223o2 164 := by
  have hc : ((-173243/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135280088167/2000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-173243/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c165 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-988089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log ((165 : ℕ)) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((165 : ℕ)) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1493549/2000000) (δ := 787/100000000) (ψ := 106031/200000) 223 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t165 : ((-769265223361/10000000000000 : ℚ) : ℝ) ≤ stT223o2 165 := by
  have hc : ((-988139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-769265223361/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-988139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c166 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-676193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log ((166 : ℕ)) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((166 : ℕ)) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5783449/10000000) (δ := 491/50000000) (ψ := 106031/200000) 223 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t166 : ((-524866680693/10000000000000 : ℚ) : ℝ) ≤ stT223o2 166 := by
  have hc : ((-676243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-524866680693/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-676243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c167 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-72847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log ((167 : ℕ)) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((167 : ℕ)) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -410927/1000000) (δ := 991/100000000) (ψ := 106031/200000) 223 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t167 : ((-881397627/156250000000 : ℚ) : ℝ) ≤ stT223o2 167 := by
  have hc : ((-72897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-881397627/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-72897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c168 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((279327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log ((168 : ℕ)) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((168 : ℕ)) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1222543/5000000) (δ := 109/12500000) (ψ := 106031/200000) 223 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t168 : ((26935745229/625000000000 : ℚ) : ℝ) ≤ stT223o2 168 := by
  have hc : ((139651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26935745229/625000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((139651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c169 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((950389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log ((169 : ℕ)) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((169 : ℕ)) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -790779/10000000) (δ := 493/50000000) (ψ := 106031/200000) 223 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t169 : ((73102926897/1000000000000 : ℚ) : ℝ) ≤ stT223o2 169 := by
  have hc : ((950339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73102926897/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((950339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c170 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((942251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log ((170 : ℕ)) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((170 : ℕ)) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 853769/10000000) (δ := 721/100000000) (ψ := 106031/200000) 223 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t170 : ((180658561941/2500000000000 : ℚ) : ℝ) ≤ stT223o2 170 := by
  have hc : ((942201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180658561941/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((942201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c171 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((54411/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log ((171 : ℕ)) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((171 : ℕ)) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2488671/10000000) (δ := 153/25000000) (ψ := 106031/200000) 223 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t171 : ((20802650957/500000000000 : ℚ) : ℝ) ≤ stT223o2 171 := by
  have hc : ((27203/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20802650957/500000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((27203/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c172 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-299/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log ((172 : ℕ)) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((172 : ℕ)) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 102851/250000) (δ := 837/100000000) (ψ := 106031/200000) 223 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t172 : ((-142586191/25000000000 : ℚ) : ℝ) ≤ stT223o2 172 := by
  have hc : ((-187/2500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142586191/25000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-187/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c173 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-132057/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log ((173 : ℕ)) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((173 : ℕ)) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5729987/10000000) (δ := 263/25000000) (ψ := 106031/200000) 223 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t173 : ((-50204345581/1000000000000 : ℚ) : ℝ) ≤ stT223o2 173 := by
  have hc : ((-132067/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50204345581/1000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-132067/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c174 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-978663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log ((174 : ℕ)) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((174 : ℕ)) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7336619/10000000) (δ := 1077/100000000) (ψ := 106031/200000) 223 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t174 : ((-741961346587/10000000000000 : ℚ) : ℝ) ≤ stT223o2 174 := by
  have hc : ((-978713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-741961346587/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-978713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c175 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-22703/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log ((175 : ℕ)) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((175 : ℕ)) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3386959/5000000) (δ := 823/100000000) (ψ := 106031/200000) 223 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t175 : ((-68651203993/1000000000000 : ℚ) : ℝ) ≤ stT223o2 175 := by
  have hc : ((-90817/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68651203993/1000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-90817/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c176 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-482443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log ((176 : ℕ)) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((176 : ℕ)) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1037119/2000000) (δ := 1043/100000000) (ψ := 106031/200000) 223 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t176 : ((-363693091047/10000000000000 : ℚ) : ℝ) ≤ stT223o2 176 := by
  have hc : ((-482493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-363693091047/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-482493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c177 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((1999/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log ((177 : ℕ)) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((177 : ℕ)) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3606271/10000000) (δ := 157/20000000) (ψ := 106031/200000) 223 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t177 : ((24031250089/2500000000000 : ℚ) : ℝ) ≤ stT223o2 177 := by
  have hc : ((63943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24031250089/2500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((63943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c178 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((13727/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log ((178 : ℕ)) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((178 : ℕ)) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -508961/2500000) (δ := 23/4000000) (ψ := 106031/200000) 223 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t178 : ((5144031253/100000000000 : ℚ) : ℝ) ≤ stT223o2 178 := by
  have hc : ((6863/10000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5144031253/100000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((6863/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c179 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((982063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log ((179 : ℕ)) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((179 : ℕ)) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -94843/2000000) (δ := 53/5000000) (ψ := 106031/200000) 223 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t179 : ((146798177331/2000000000000 : ℚ) : ℝ) ≤ stT223o2 179 := by
  have hc : ((982013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146798177331/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((982013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c180 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((181669/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log ((180 : ℕ)) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((180 : ℕ)) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 539357/5000000) (δ := 71/12500000) (ψ := 106031/200000) 223 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t180 : ((27080088789/400000000000 : ℚ) : ℝ) ≤ stT223o2 180 := by
  have hc : ((181659/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27080088789/400000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((181659/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c181 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((498251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log ((181 : ℕ)) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((181 : ℕ)) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2623039/10000000) (δ := 39/5000000) (ψ := 106031/200000) 223 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t181 : ((185154907047/5000000000000 : ℚ) : ℝ) ≤ stT223o2 181 := by
  have hc : ((498201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185154907047/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((498201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c182 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-92613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log ((182 : ℕ)) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((182 : ℕ)) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 831771/2000000) (δ := 469/50000000) (ψ := 106031/200000) 223 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t182 : ((-54949159/8000000000 : ℚ) : ℝ) ≤ stT223o2 182 := by
  have hc : ((-92663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54949159/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-92663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c183 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-80881/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log ((183 : ℕ)) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((183 : ℕ)) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 355391/625000) (δ := 113/20000000) (ψ := 106031/200000) 223 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t183 : ((-119587269439/2500000000000 : ℚ) : ℝ) ≤ stT223o2 183 := by
  have hc : ((-323549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119587269439/2500000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-323549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c184 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-966529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log ((184 : ℕ)) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((184 : ℕ)) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3602667/5000000) (δ := 633/100000000) (ψ := 106031/200000) 223 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t184 : ((-71257170459/1000000000000 : ℚ) : ℝ) ≤ stT223o2 184 := by
  have hc : ((-966579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71257170459/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-966579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c185 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-941117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log ((185 : ℕ)) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((185 : ℕ)) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3495893/5000000) (δ := 87/10000000) (ψ := 106031/200000) 223 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t185 : ((-138392019181/2000000000000 : ℚ) : ℝ) ≤ stT223o2 185 := by
  have hc : ((-941167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138392019181/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-941167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c186 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-292483/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log ((186 : ℕ)) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((186 : ℕ)) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5489087/10000000) (δ := 197/25000000) (ψ := 106031/200000) 223 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t186 : ((-13404837243/312500000000 : ℚ) : ℝ) ≤ stT223o2 186 := by
  have hc : ((-73127/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13404837243/312500000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-73127/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c187 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-13489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log ((187 : ℕ)) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((187 : ℕ)) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -798889/2000000) (δ := 19/2000000) (ψ := 106031/200000) 223 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t187 : ((-4941211661/2500000000000 : ℚ) : ℝ) ≤ stT223o2 187 := by
  have hc : ((-6757/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4941211661/2500000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-6757/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c188 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((537683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log ((188 : ℕ)) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((188 : ℕ)) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -100311/400000) (δ := 673/100000000) (ψ := 106031/200000) 223 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t188 : ((98027162523/2500000000000 : ℚ) : ℝ) ≤ stT223o2 188 := by
  have hc : ((537633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98027162523/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((537633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c189 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((916483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log ((189 : ℕ)) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((189 : ℕ)) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1028991/10000000) (δ := 19/2000000) (ψ := 106031/200000) 223 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t189 : ((20831438523/312500000000 : ℚ) : ℝ) ≤ stT223o2 189 := by
  have hc : ((916433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20831438523/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((916433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c190 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((246103/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log ((190 : ℕ)) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((190 : ℕ)) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 110497/2500000) (δ := 389/50000000) (ψ := 106031/200000) 223 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t190 : ((89266375789/1250000000000 : ℚ) : ℝ) ≤ stT223o2 190 := by
  have hc : ((492181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89266375789/1250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((492181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c191 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((723389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log ((191 : ℕ)) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((191 : ℕ)) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 952623/5000000) (δ := 83/10000000) (ψ := 106031/200000) 223 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t191 : ((261694646793/5000000000000 : ℚ) : ℝ) ≤ stT223o2 191 := by
  have hc : ((723339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261694646793/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((723339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c192 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((224521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log ((192 : ℕ)) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((192 : ℕ)) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3360863/10000000) (δ := 783/100000000) (ψ := 106031/200000) 223 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t192 : ((161997802577/10000000000000 : ℚ) : ℝ) ≤ stT223o2 192 := by
  have hc : ((224471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161997802577/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((224471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c193 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-345499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log ((193 : ℕ)) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((193 : ℕ)) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2404459/5000000) (δ := 963/100000000) (ψ := 106031/200000) 223 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t193 : ((-31091462373/1250000000000 : ℚ) : ℝ) ≤ stT223o2 193 := by
  have hc : ((-345549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31091462373/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-345549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c194 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-400511/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log ((194 : ℕ)) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((194 : ℕ)) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 624949/1000000) (δ := 643/100000000) (ψ := 106031/200000) 223 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t194 : ((-35946053253/625000000000 : ℚ) : ℝ) ≤ stT223o2 194 := by
  have hc : ((-50067/62500 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35946053253/625000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-50067/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c195 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-997653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log ((195 : ℕ)) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((195 : ℕ)) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1536531/2000000) (δ := 633/100000000) (ψ := 106031/200000) 223 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t195 : ((-142894016769/2000000000000 : ℚ) : ℝ) ≤ stT223o2 195 := by
  have hc : ((-997703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142894016769/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-997703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c196 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-876717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log ((196 : ℕ)) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((196 : ℕ)) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3299737/5000000) (δ := 639/100000000) (ψ := 106031/200000) 223 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t196 : ((-313131196681/5000000000000 : ℚ) : ℝ) ≤ stT223o2 196 := by
  have hc : ((-876767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-313131196681/5000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-876767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c197 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-120199/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log ((197 : ℕ)) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((197 : ℕ)) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -161903/312500) (δ := 103/12500000) (ψ := 106031/200000) 223 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t197 : ((-171294415233/5000000000000 : ℚ) : ℝ) ≤ stT223o2 197 := by
  have hc : ((-240423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171294415233/5000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-240423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c198 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((12591/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log ((198 : ℕ)) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((198 : ℕ)) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7539/20000) (δ := 779/100000000) (ψ := 106031/200000) 223 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t198 : ((8940926689/2000000000000 : ℚ) : ℝ) ≤ stT223o2 198 := by
  have hc : ((12581/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8940926689/2000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((12581/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c199 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((292431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log ((199 : ℕ)) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((199 : ℕ)) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -473043/2000000) (δ := 849/100000000) (ψ := 106031/200000) 223 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t199 : ((103640528843/2500000000000 : ℚ) : ℝ) ≤ stT223o2 199 := by
  have hc : ((146203/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103640528843/2500000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((146203/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c200 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((37039/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log ((200 : ℕ)) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((200 : ℕ)) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -967969/10000000) (δ := 367/50000000) (ψ := 106031/200000) 223 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t200 : ((13094542461/200000000000 : ℚ) : ℝ) ≤ stT223o2 200 := by
  have hc : ((37037/40000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13094542461/200000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((37037/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c201 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((492883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log ((201 : ℕ)) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((201 : ℕ)) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 105577/2500000) (δ := 261/25000000) (ψ := 106031/200000) 223 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t201 : ((34763492601/500000000000 : ℚ) : ℝ) ≤ stT223o2 201 := by
  have hc : ((246429/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34763492601/500000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((246429/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c202 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((23447/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log ((202 : ℕ)) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((202 : ℕ)) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 361137/2000000) (δ := 1049/100000000) (ψ := 106031/200000) 223 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t202 : ((263938231819/5000000000000 : ℚ) : ℝ) ≤ stT223o2 202 := by
  have hc : ((375127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((263938231819/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((375127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c203 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((293517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log ((203 : ℕ)) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((203 : ℕ)) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3182231/10000000) (δ := 211/25000000) (ψ := 106031/200000) 223 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t203 : ((102986667777/5000000000000 : ℚ) : ℝ) ≤ stT223o2 203 := by
  have hc : ((293467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102986667777/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((293467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c204 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-247413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log ((204 : ℕ)) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((204 : ℕ)) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4552013/10000000) (δ := 4/390625) (ψ := 106031/200000) 223 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t204 : ((-173258992283/10000000000000 : ℚ) : ℝ) ≤ stT223o2 204 := by
  have hc : ((-247463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173258992283/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-247463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c205 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-714033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log ((205 : ℕ)) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((205 : ℕ)) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 739387/1250000) (δ := 211/25000000) (ψ := 106031/200000) 223 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t205 : ((-498737703773/10000000000000 : ℚ) : ℝ) ≤ stT223o2 205 := by
  have hc : ((-714083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-498737703773/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-714083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c206 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-121623/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log ((206 : ℕ)) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((206 : ℕ)) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7271547/10000000) (δ := 377/50000000) (ψ := 106031/200000) 223 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t206 : ((-169486467739/2500000000000 : ℚ) : ℝ) ≤ stT223o2 206 := by
  have hc : ((-486517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169486467739/2500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-486517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c207 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-953251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log ((207 : ℕ)) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((207 : ℕ)) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1417307/2000000) (δ := 203/20000000) (ψ := 106031/200000) 223 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t207 : ((-662590906749/10000000000000 : ℚ) : ℝ) ≤ stT223o2 207 := by
  have hc : ((-953301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-662590906749/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-953301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c208 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-664233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log ((208 : ℕ)) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((208 : ℕ)) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5743159/10000000) (δ := 43/5000000) (ψ := 106031/200000) 223 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t208 : ((-3598421011/78125000000 : ℚ) : ℝ) ≤ stT223o2 208 := by
  have hc : ((-664283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3598421011/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-664283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c209 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-95261/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log ((209 : ℕ)) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((209 : ℕ)) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2203113/5000000) (δ := 71/12500000) (ψ := 106031/200000) 223 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t209 : ((-6591075549/500000000000 : ℚ) : ℝ) ≤ stT223o2 209 := by
  have hc : ((-47643/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6591075549/500000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-47643/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c210 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((10437/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log ((210 : ℕ)) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((210 : ℕ)) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1537837/5000000) (δ := 783/100000000) (ψ := 106031/200000) 223 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t210 : ((23043616571/1000000000000 : ℚ) : ℝ) ≤ stT223o2 210 := by
  have hc : ((166967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23043616571/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((166967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c211 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((76447/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log ((211 : ℕ)) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((211 : ℕ)) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -437861/2500000) (δ := 773/100000000) (ψ := 106031/200000) 223 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t211 : ((6578101647/125000000000 : ℚ) : ℝ) ≤ stT223o2 211 := by
  have hc : ((38221/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6578101647/125000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((38221/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c212 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((492503/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log ((212 : ℕ)) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((212 : ℕ)) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -216737/5000000) (δ := 83/10000000) (ψ := 106031/200000) 223 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t212 : ((84558718839/1250000000000 : ℚ) : ℝ) ≤ stT223o2 212 := by
  have hc : ((246239/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84558718839/1250000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((246239/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c213 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((23473/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log ((213 : ℕ)) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((213 : ℕ)) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 878293/10000000) (δ := 29/4000000) (ψ := 106031/200000) 223 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t213 : ((16082561439/250000000000 : ℚ) : ℝ) ≤ stT223o2 213 := by
  have hc : ((93887/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16082561439/250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((93887/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c214 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((642097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log ((214 : ℕ)) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((214 : ℕ)) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 545979/2500000) (δ := 479/50000000) (ψ := 106031/200000) 223 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t214 : ((87778739699/2000000000000 : ℚ) : ℝ) ≤ stT223o2 214 := by
  have hc : ((642047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87778739699/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((642047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c215 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((88243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log ((215 : ℕ)) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((215 : ℕ)) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 870863/2500000) (δ := 409/50000000) (ψ := 106031/200000) 223 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t215 : ((15041036673/1250000000000 : ℚ) : ℝ) ≤ stT223o2 215 := by
  have hc : ((44109/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15041036673/1250000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((44109/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c216 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-13339/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log ((216 : ℕ)) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((216 : ℕ)) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2388479/5000000) (δ := 519/50000000) (ψ := 106031/200000) 223 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t216 : ((-4538701587/200000000000 : ℚ) : ℝ) ≤ stT223o2 216 := by
  have hc : ((-13341/40000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4538701587/200000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-13341/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c217 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-75457/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log ((217 : ℕ)) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((217 : ℕ)) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6064489/10000000) (δ := 117/20000000) (ψ := 106031/200000) 223 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t217 : ((-5122700139/100000000000 : ℚ) : ℝ) ≤ stT223o2 217 := by
  have hc : ((-37731/50000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5122700139/100000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-37731/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c218 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-195887/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log ((218 : ℕ)) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((218 : ℕ)) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 73461/100000) (δ := 67/10000000) (ψ := 106031/200000) 223 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t218 : ((-66339147771/1000000000000 : ℚ) : ℝ) ≤ stT223o2 218 := by
  have hc : ((-195897/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66339147771/1000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-195897/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c219 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-2383/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log ((219 : ℕ)) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((219 : ℕ)) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7086117/10000000) (δ := 803/100000000) (ψ := 106031/200000) 223 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t219 : ((-1288294497/20000000000 : ℚ) : ℝ) ≤ stT223o2 219 := by
  have hc : ((-3813/4000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1288294497/20000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-3813/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c220 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-685781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log ((220 : ℕ)) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((220 : ℕ)) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5816183/10000000) (δ := 613/100000000) (ψ := 106031/200000) 223 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t220 : ((-2311936301/50000000000 : ℚ) : ℝ) ≤ stT223o2 220 := by
  have hc : ((-685831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2311936301/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-685831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c221 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-247411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log ((221 : ℕ)) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((221 : ℕ)) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4552009/10000000) (δ := 1133/100000000) (ψ := 106031/200000) 223 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t221 : ((-166460333253/10000000000000 : ℚ) : ℝ) ≤ stT223o2 221 := by
  have hc : ((-247461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166460333253/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-247461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c222 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((250677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log ((222 : ℕ)) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((222 : ℕ)) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1646771/5000000) (δ := 7/800000) (ψ := 106031/200000) 223 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t222 : ((42052453703/2500000000000 : ℚ) : ℝ) ≤ stT223o2 222 := by
  have hc : ((250627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42052453703/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((250627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c223 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((10702/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log ((223 : ℕ)) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((223 : ℕ)) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -204073/1000000) (δ := 159/20000000) (ψ := 106031/200000) 223 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t223 : ((229313933911/5000000000000 : ℚ) : ℝ) ≤ stT223o2 223 := by
  have hc : ((342439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229313933911/5000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((342439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c224 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((950047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log ((224 : ℕ)) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((224 : ℕ)) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -31741/400000) (δ := 71/12500000) (ψ := 106031/200000) 223 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t224 : ((634743345541/10000000000000 : ℚ) : ℝ) ≤ stT223o2 224 := by
  have hc : ((949997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((634743345541/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((949997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c225 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((491989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log ((225 : ℕ)) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((225 : ℕ)) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 717/16000) (δ := 141/12500000) (ψ := 106031/200000) 223 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t225 : ((40996959003/625000000000 : ℚ) : ℝ) ≤ stT223o2 225 := by
  have hc : ((122991/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40996959003/625000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((122991/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c226 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((390757/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log ((226 : ℕ)) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((226 : ℕ)) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1684269/10000000) (δ := 579/50000000) (ψ := 106031/200000) 223 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t226 : ((6497775477/125000000000 : ℚ) : ℝ) ≤ stT223o2 226 := by
  have hc : ((97683/125000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6497775477/125000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((97683/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c227 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((49231/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log ((227 : ℕ)) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((227 : ℕ)) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 728739/2500000) (δ := 29/3125000) (ψ := 106031/200000) 223 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t227 : ((130686394977/5000000000000 : ℚ) : ℝ) ≤ stT223o2 227 := by
  have hc : ((196899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130686394977/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((196899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c228 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-85193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log ((228 : ℕ)) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((228 : ℕ)) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 517529/1250000) (δ := 207/25000000) (ψ := 106031/200000) 223 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t228 : ((-56453625881/10000000000000 : ℚ) : ℝ) ≤ stT223o2 228 := by
  have hc : ((-85243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56453625881/10000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-85243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c229 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-67797/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log ((229 : ℕ)) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((229 : ℕ)) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5360147/10000000) (δ := 17/1562500) (ψ := 106031/200000) 223 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t229 : ((-179222703447/5000000000000 : ℚ) : ℝ) ≤ stT223o2 229 := by
  have hc : ((-271213/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179222703447/5000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-271213/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c230 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-217979/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log ((230 : ℕ)) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((230 : ℕ)) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3287373/5000000) (δ := 1023/100000000) (ψ := 106031/200000) 223 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t230 : ((-287478906523/5000000000000 : ℚ) : ℝ) ≤ stT223o2 230 := by
  have hc : ((-435983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-287478906523/5000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-435983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c231 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-999609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log ((231 : ℕ)) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((231 : ℕ)) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 311363/400000) (δ := 1023/100000000) (ψ := 106031/200000) 223 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t231 : ((-20553988699/312500000000 : ℚ) : ℝ) ≤ stT223o2 231 := by
  have hc : ((-999659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20553988699/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-999659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c232 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-898841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log ((232 : ℕ)) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((232 : ℕ)) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6719783/10000000) (δ := 383/50000000) (ψ := 106031/200000) 223 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t232 : ((-590151604903/10000000000000 : ℚ) : ℝ) ≤ stT223o2 232 := by
  have hc : ((-898891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-590151604903/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-898891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c233 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-23809/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log ((233 : ℕ)) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((233 : ℕ)) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -690107/1250000) (δ := 581/100000000) (ψ := 106031/200000) 223 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t233 : ((-7799554971/200000000000 : ℚ) : ℝ) ≤ stT223o2 233 := by
  have hc : ((-23811/40000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7799554971/200000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-23811/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c234 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-159347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log ((234 : ℕ)) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((234 : ℕ)) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -540883/1250000) (δ := 481/50000000) (ψ := 106031/200000) 223 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t234 : ((-104201166237/10000000000000 : ℚ) : ℝ) ≤ stT223o2 234 := by
  have hc : ((-159397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104201166237/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-159397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c235 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((62049/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log ((235 : ℕ)) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((235 : ℕ)) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3138363/10000000) (δ := 491/50000000) (ψ := 106031/200000) 223 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t235 : ((5058722099/250000000000 : ℚ) : ℝ) ≤ stT223o2 235 := by
  have hc : ((62039/200000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5058722099/250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((62039/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c236 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((177397/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log ((236 : ℕ)) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((236 : ℕ)) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1954709/10000000) (δ := 1067/100000000) (ψ := 106031/200000) 223 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t236 : ((3608355499/78125000000 : ℚ) : ℝ) ≤ stT223o2 236 := by
  have hc : ((354769/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3608355499/78125000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((354769/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c237 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((238051/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log ((237 : ℕ)) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((237 : ℕ)) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -776061/10000000) (δ := 173/25000000) (ψ := 106031/200000) 223 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t237 : ((309244860813/5000000000000 : ℚ) : ℝ) ≤ stT223o2 237 := by
  have hc : ((476077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((309244860813/5000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((476077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c238 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((493689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log ((238 : ℕ)) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((238 : ℕ)) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3181/80000) (δ := 791/100000000) (ψ := 106031/200000) 223 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t238 : ((9999827681/156250000000 : ℚ) : ℝ) ≤ stT223o2 238 := by
  have hc : ((15427/15625 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9999827681/156250000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((15427/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c239 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((202513/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log ((239 : ℕ)) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((239 : ℕ)) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 156639/1000000) (δ := 281/50000000) (ψ := 106031/200000) 223 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t239 : ((130986638423/2500000000000 : ℚ) : ℝ) ≤ stT223o2 239 := by
  have hc : ((405001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130986638423/2500000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((405001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c240 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((230307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log ((240 : ℕ)) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((240 : ℕ)) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 109211/400000) (δ := 109/12500000) (ψ := 106031/200000) 223 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t240 : ((74323170077/2500000000000 : ℚ) : ℝ) ≤ stT223o2 240 := by
  have hc : ((115141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74323170077/2500000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((115141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c241 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((3767/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log ((241 : ℕ)) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((241 : ℕ)) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 97233/250000) (δ := 193/25000000) (ψ := 106031/200000) 223 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t241 : ((1209241851/1250000000000 : ℚ) : ℝ) ≤ stT223o2 241 := by
  have hc : ((7509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1209241851/1250000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((7509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c242 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-431929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log ((242 : ℕ)) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((242 : ℕ)) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2521783/5000000) (δ := 213/25000000) (ψ := 106031/200000) 223 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t242 : ((-11107476027/400000000000 : ℚ) : ℝ) ≤ stT223o2 242 := by
  have hc : ((-431979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11107476027/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-431979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c243 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-98413/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log ((243 : ℕ)) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((243 : ℕ)) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1548263/2500000) (δ := 667/100000000) (ψ := 106031/200000) 223 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t243 : ((-252544189177/5000000000000 : ℚ) : ℝ) ≤ stT223o2 243 := by
  have hc : ((-393677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252544189177/5000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-393677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c244 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-489381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log ((244 : ℕ)) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((244 : ℕ)) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3668909/5000000) (δ := 847/100000000) (ψ := 106031/200000) 223 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t244 : ((-31331038011/500000000000 : ℚ) : ℝ) ≤ stT223o2 244 := by
  have hc : ((-244703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31331038011/500000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-244703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c245 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-969019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log ((245 : ℕ)) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((245 : ℕ)) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3615031/5000000) (δ := 1217/100000000) (ψ := 106031/200000) 223 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t245 : ((-619115895513/10000000000000 : ℚ) : ℝ) ≤ stT223o2 245 := by
  have hc : ((-969069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-619115895513/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-969069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c246 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-30497/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log ((246 : ℕ)) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((246 : ℕ)) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6094623/10000000) (δ := 751/100000000) (ψ := 106031/200000) 223 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t246 : ((-19445460923/400000000000 : ℚ) : ℝ) ≤ stT223o2 246 := by
  have hc : ((-30499/40000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19445460923/400000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-30499/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c247 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-402933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log ((247 : ℕ)) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((247 : ℕ)) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4963789/10000000) (δ := 711/100000000) (ψ := 106031/200000) 223 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t247 : ((-51282407631/2000000000000 : ℚ) : ℝ) ≤ stT223o2 247 := by
  have hc : ((-402983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51282407631/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-402983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c248 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((35779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log ((248 : ℕ)) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((248 : ℕ)) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -153501/400000) (δ := 611/100000000) (ψ := 106031/200000) 223 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t248 : ((4537583/2000000000 : ℚ) : ℝ) ≤ stT223o2 248 := by
  have hc : ((35729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4537583/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((35729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c249 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((465747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log ((249 : ℕ)) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((249 : ℕ)) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2715793/10000000) (δ := 67/6250000) (ψ := 106031/200000) 223 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t249 : ((73780841407/2500000000000 : ℚ) : ℝ) ≤ stT223o2 249 := by
  have hc : ((465697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73780841407/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((465697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_c250 :
    |Real.cos (((223 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((20061/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log ((250 : ℕ)) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((250 : ℕ)) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1598557/10000000) (δ := 921/100000000) (ψ := 106031/200000) 223 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st223o2_t250 : ((10149511349/200000000000 : ℚ) : ℝ) ≤ stT223o2 250 := by
  have hc : ((80239/100000 : ℚ) : ℝ)
      ≤ Real.cos (((223 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st223o2_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10149511349/200000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((80239/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st223o2_p1 : ((862679/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT223o2 (i+1) := by
  rw [Finset.sum_range_one]
  exact st223o2_t1

theorem st223o2_p2 : ((5061520959667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 1, stT223o2 (i+1)) + stT223o2 2 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 1
    simpa using h
  have hprev := st223o2_p1
  have hstep := st223o2_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p3 : ((2610969158323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 2, stT223o2 (i+1)) + stT223o2 3 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 2
    simpa using h
  have hprev := st223o2_p2
  have hstep := st223o2_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p4 : ((6212683049/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 3, stT223o2 (i+1)) + stT223o2 4 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 3
    simpa using h
  have hprev := st223o2_p3
  have hstep := st223o2_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p5 : ((-521820050231/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 4, stT223o2 (i+1)) + stT223o2 5 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 4
    simpa using h
  have hprev := st223o2_p4
  have hstep := st223o2_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p6 : ((-2572805821631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 5, stT223o2 (i+1)) + stT223o2 6 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 5
    simpa using h
  have hprev := st223o2_p5
  have hstep := st223o2_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p7 : ((-1090024472929/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 6, stT223o2 (i+1)) + stT223o2 7 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 6
    simpa using h
  have hprev := st223o2_p6
  have hstep := st223o2_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p8 : ((-3638527426213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 7, stT223o2 (i+1)) + stT223o2 8 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 7
    simpa using h
  have hprev := st223o2_p7
  have hstep := st223o2_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p9 : ((-4496051797193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 8, stT223o2 (i+1)) + stT223o2 9 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 8
    simpa using h
  have hprev := st223o2_p8
  have hstep := st223o2_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p10 : ((-3966566460867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 9, stT223o2 (i+1)) + stT223o2 10 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 9
    simpa using h
  have hprev := st223o2_p9
  have hstep := st223o2_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p11 : ((-6921604314417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 10, stT223o2 (i+1)) + stT223o2 11 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 10
    simpa using h
  have hprev := st223o2_p10
  have hstep := st223o2_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p12 : ((-4043502020413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 11, stT223o2 (i+1)) + stT223o2 12 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 11
    simpa using h
  have hprev := st223o2_p11
  have hstep := st223o2_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p13 : ((-6572424608229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 12, stT223o2 (i+1)) + stT223o2 13 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 12
    simpa using h
  have hprev := st223o2_p12
  have hstep := st223o2_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p14 : ((-6610445200767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 13, stT223o2 (i+1)) + stT223o2 14 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 13
    simpa using h
  have hprev := st223o2_p13
  have hstep := st223o2_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p15 : ((-4068224979943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 14, stT223o2 (i+1)) + stT223o2 15 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 14
    simpa using h
  have hprev := st223o2_p14
  have hstep := st223o2_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p16 : ((-2217814979943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 15, stT223o2 (i+1)) + stT223o2 16 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 15
    simpa using h
  have hprev := st223o2_p15
  have hstep := st223o2_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p17 : ((-1370519286699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 16, stT223o2 (i+1)) + stT223o2 17 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 16
    simpa using h
  have hprev := st223o2_p16
  have hstep := st223o2_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p18 : ((-5990988723/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 17, stT223o2 (i+1)) + stT223o2 18 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 17
    simpa using h
  have hprev := st223o2_p17
  have hstep := st223o2_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p19 : ((394199311503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 18, stT223o2 (i+1)) + stT223o2 19 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 18
    simpa using h
  have hprev := st223o2_p18
  have hstep := st223o2_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p20 : ((1186050598009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 19, stT223o2 (i+1)) + stT223o2 20 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 19
    simpa using h
  have hprev := st223o2_p19
  have hstep := st223o2_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p21 : ((1103971912359/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 20, stT223o2 (i+1)) + stT223o2 21 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 20
    simpa using h
  have hprev := st223o2_p20
  have hstep := st223o2_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p22 : ((1165996260003/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 21, stT223o2 (i+1)) + stT223o2 22 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 21
    simpa using h
  have hprev := st223o2_p21
  have hstep := st223o2_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p23 : ((678222460443/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 22, stT223o2 (i+1)) + stT223o2 23 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 22
    simpa using h
  have hprev := st223o2_p22
  have hstep := st223o2_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p24 : ((964901024793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 23, stT223o2 (i+1)) + stT223o2 24 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 23
    simpa using h
  have hprev := st223o2_p23
  have hstep := st223o2_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p25 : ((1937844024793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 24, stT223o2 (i+1)) + stT223o2 25 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 24
    simpa using h
  have hprev := st223o2_p24
  have hstep := st223o2_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p26 : ((91685659333/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 25, stT223o2 (i+1)) + stT223o2 26 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 25
    simpa using h
  have hprev := st223o2_p25
  have hstep := st223o2_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p27 : ((418134616303/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 26, stT223o2 (i+1)) + stT223o2 27 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 26
    simpa using h
  have hprev := st223o2_p26
  have hstep := st223o2_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p28 : ((3894472273897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 27, stT223o2 (i+1)) + stT223o2 28 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 27
    simpa using h
  have hprev := st223o2_p27
  have hstep := st223o2_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p29 : ((3009013470261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 28, stT223o2 (i+1)) + stT223o2 29 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 28
    simpa using h
  have hprev := st223o2_p28
  have hstep := st223o2_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p30 : ((2751552810647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 29, stT223o2 (i+1)) + stT223o2 30 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 29
    simpa using h
  have hprev := st223o2_p29
  have hstep := st223o2_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p31 : ((384684160769/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 30, stT223o2 (i+1)) + stT223o2 31 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 30
    simpa using h
  have hprev := st223o2_p30
  have hstep := st223o2_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p32 : ((1154792176711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 31, stT223o2 (i+1)) + stT223o2 32 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 31
    simpa using h
  have hprev := st223o2_p31
  have hstep := st223o2_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p33 : ((2002797278903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 32, stT223o2 (i+1)) + stT223o2 33 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 32
    simpa using h
  have hprev := st223o2_p32
  have hstep := st223o2_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p34 : ((572974128073/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 33, stT223o2 (i+1)) + stT223o2 34 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 33
    simpa using h
  have hprev := st223o2_p33
  have hstep := st223o2_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p35 : ((7959933089/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 34, stT223o2 (i+1)) + stT223o2 35 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 34
    simpa using h
  have hprev := st223o2_p34
  have hstep := st223o2_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p36 : ((2315294544899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 35, stT223o2 (i+1)) + stT223o2 36 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 35
    simpa using h
  have hprev := st223o2_p35
  have hstep := st223o2_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p37 : ((3958096584841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 36, stT223o2 (i+1)) + stT223o2 37 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 36
    simpa using h
  have hprev := st223o2_p36
  have hstep := st223o2_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p38 : ((2369685301011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 37, stT223o2 (i+1)) + stT223o2 38 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 37
    simpa using h
  have hprev := st223o2_p37
  have hstep := st223o2_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p39 : ((762284213459/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 38, stT223o2 (i+1)) + stT223o2 39 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 38
    simpa using h
  have hprev := st223o2_p38
  have hstep := st223o2_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p40 : ((2674831946257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 39, stT223o2 (i+1)) + stT223o2 40 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 39
    simpa using h
  have hprev := st223o2_p39
  have hstep := st223o2_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p41 : ((825641862049/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 40, stT223o2 (i+1)) + stT223o2 41 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 40
    simpa using h
  have hprev := st223o2_p40
  have hstep := st223o2_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p42 : ((336576699381/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 41, stT223o2 (i+1)) + stT223o2 42 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 41
    simpa using h
  have hprev := st223o2_p41
  have hstep := st223o2_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p43 : ((1278490759397/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 42, stT223o2 (i+1)) + stT223o2 43 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 42
    simpa using h
  have hprev := st223o2_p42
  have hstep := st223o2_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p44 : ((1962483992157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 43, stT223o2 (i+1)) + stT223o2 44 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 43
    simpa using h
  have hprev := st223o2_p43
  have hstep := st223o2_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p45 : ((1232290023909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 44, stT223o2 (i+1)) + stT223o2 45 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 44
    simpa using h
  have hprev := st223o2_p44
  have hstep := st223o2_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p46 : ((3388806328197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 45, stT223o2 (i+1)) + stT223o2 46 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 45
    simpa using h
  have hprev := st223o2_p45
  have hstep := st223o2_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p47 : ((2788058229/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 46, stT223o2 (i+1)) + stT223o2 47 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 46
    simpa using h
  have hprev := st223o2_p46
  have hstep := st223o2_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p48 : ((1195465134853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 47, stT223o2 (i+1)) + stT223o2 48 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 47
    simpa using h
  have hprev := st223o2_p47
  have hstep := st223o2_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p49 : ((190350349387/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 48, stT223o2 (i+1)) + stT223o2 49 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 48
    simpa using h
  have hprev := st223o2_p48
  have hstep := st223o2_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p50 : ((76698822337/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 49, stT223o2 (i+1)) + stT223o2 50 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 49
    simpa using h
  have hprev := st223o2_p49
  have hstep := st223o2_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p51 : ((2543588267129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 50, stT223o2 (i+1)) + stT223o2 51 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 50
    simpa using h
  have hprev := st223o2_p50
  have hstep := st223o2_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p52 : ((3899645329379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 51, stT223o2 (i+1)) + stT223o2 52 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 51
    simpa using h
  have hprev := st223o2_p51
  have hstep := st223o2_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p53 : ((2949666287809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 52, stT223o2 (i+1)) + stT223o2 53 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 52
    simpa using h
  have hprev := st223o2_p52
  have hstep := st223o2_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p54 : ((2555521509201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 53, stT223o2 (i+1)) + stT223o2 54 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 53
    simpa using h
  have hprev := st223o2_p53
  have hstep := st223o2_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p55 : ((30326120241/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 54, stT223o2 (i+1)) + stT223o2 55 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 54
    simpa using h
  have hprev := st223o2_p54
  have hstep := st223o2_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p56 : ((31056643923/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 55, stT223o2 (i+1)) + stT223o2 56 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 55
    simpa using h
  have hprev := st223o2_p55
  have hstep := st223o2_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p57 : ((482998656423/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 56, stT223o2 (i+1)) + stT223o2 57 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 56
    simpa using h
  have hprev := st223o2_p56
  have hstep := st223o2_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p58 : ((741350563743/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 57, stT223o2 (i+1)) + stT223o2 58 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 57
    simpa using h
  have hprev := st223o2_p57
  have hstep := st223o2_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p59 : ((701106540063/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 58, stT223o2 (i+1)) + stT223o2 59 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 58
    simpa using h
  have hprev := st223o2_p58
  have hstep := st223o2_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p60 : ((234771287153/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 59, stT223o2 (i+1)) + stT223o2 60 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 59
    simpa using h
  have hprev := st223o2_p59
  have hstep := st223o2_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p61 : ((1601005765901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 60, stT223o2 (i+1)) + stT223o2 61 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 60
    simpa using h
  have hprev := st223o2_p60
  have hstep := st223o2_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p62 : ((3916942084739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 61, stT223o2 (i+1)) + stT223o2 62 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 61
    simpa using h
  have hprev := st223o2_p61
  have hstep := st223o2_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p63 : ((2749105803777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 62, stT223o2 (i+1)) + stT223o2 63 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 62
    simpa using h
  have hprev := st223o2_p62
  have hstep := st223o2_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p64 : ((1250593427721/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 63, stT223o2 (i+1)) + stT223o2 64 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 63
    simpa using h
  have hprev := st223o2_p63
  have hstep := st223o2_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p65 : ((3740393976549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 64, stT223o2 (i+1)) + stT223o2 65 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 64
    simpa using h
  have hprev := st223o2_p64
  have hstep := st223o2_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p66 : ((1814947983957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 65, stT223o2 (i+1)) + stT223o2 66 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 65
    simpa using h
  have hprev := st223o2_p65
  have hstep := st223o2_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p67 : ((2431475479359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 66, stT223o2 (i+1)) + stT223o2 67 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 66
    simpa using h
  have hprev := st223o2_p66
  have hstep := st223o2_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p68 : ((2762874910521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 67, stT223o2 (i+1)) + stT223o2 68 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 67
    simpa using h
  have hprev := st223o2_p67
  have hstep := st223o2_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p69 : ((3900216144447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 68, stT223o2 (i+1)) + stT223o2 69 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 68
    simpa using h
  have hprev := st223o2_p68
  have hstep := st223o2_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p70 : ((3470875544899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 69, stT223o2 (i+1)) + stT223o2 70 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 69
    simpa using h
  have hprev := st223o2_p69
  have hstep := st223o2_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p71 : ((2367886288009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 70, stT223o2 (i+1)) + stT223o2 71 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 70
    simpa using h
  have hprev := st223o2_p70
  have hstep := st223o2_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p72 : ((2790509760697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 71, stT223o2 (i+1)) + stT223o2 72 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 71
    simpa using h
  have hprev := st223o2_p71
  have hstep := st223o2_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p73 : ((3896187669109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 72, stT223o2 (i+1)) + stT223o2 73 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 72
    simpa using h
  have hprev := st223o2_p72
  have hstep := st223o2_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p74 : ((3574623281369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 73, stT223o2 (i+1)) + stT223o2 74 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 73
    simpa using h
  have hprev := st223o2_p73
  have hstep := st223o2_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p75 : ((2444300328881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 74, stT223o2 (i+1)) + stT223o2 75 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 74
    simpa using h
  have hprev := st223o2_p74
  have hstep := st223o2_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p76 : ((2572606738571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 75, stT223o2 (i+1)) + stT223o2 76 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 75
    simpa using h
  have hprev := st223o2_p75
  have hstep := st223o2_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p77 : ((928038404679/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 76, stT223o2 (i+1)) + stT223o2 77 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 76
    simpa using h
  have hprev := st223o2_p76
  have hstep := st223o2_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p78 : ((3862455464527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 77, stT223o2 (i+1)) + stT223o2 78 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 77
    simpa using h
  have hprev := st223o2_p77
  have hstep := st223o2_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p79 : ((2782247224847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 78, stT223o2 (i+1)) + stT223o2 79 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 78
    simpa using h
  have hprev := st223o2_p78
  have hstep := st223o2_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p80 : ((2294030845931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 79, stT223o2 (i+1)) + stT223o2 80 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 79
    simpa using h
  have hprev := st223o2_p79
  have hstep := st223o2_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p81 : ((159341482277/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 80, stT223o2 (i+1)) + stT223o2 81 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 80
    simpa using h
  have hprev := st223o2_p80
  have hstep := st223o2_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p82 : ((801849893687/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 81, stT223o2 (i+1)) + stT223o2 82 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 81
    simpa using h
  have hprev := st223o2_p81
  have hstep := st223o2_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p83 : ((868020959863/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 82, stT223o2 (i+1)) + stT223o2 83 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 82
    simpa using h
  have hprev := st223o2_p82
  have hstep := st223o2_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p84 : ((18923402969/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 83, stT223o2 (i+1)) + stT223o2 84 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 83
    simpa using h
  have hprev := st223o2_p83
  have hstep := st223o2_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p85 : ((612210014103/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 84, stT223o2 (i+1)) + stT223o2 85 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 84
    simpa using h
  have hprev := st223o2_p84
  have hstep := st223o2_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p86 : ((69913468761/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 85, stT223o2 (i+1)) + stT223o2 86 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 85
    simpa using h
  have hprev := st223o2_p85
  have hstep := st223o2_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p87 : ((403189561541/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 86, stT223o2 (i+1)) + stT223o2 87 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 86
    simpa using h
  have hprev := st223o2_p86
  have hstep := st223o2_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p88 : ((1652425519649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 87, stT223o2 (i+1)) + stT223o2 88 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 87
    simpa using h
  have hprev := st223o2_p87
  have hstep := st223o2_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p89 : ((586392187317/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 88, stT223o2 (i+1)) + stT223o2 89 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 88
    simpa using h
  have hprev := st223o2_p88
  have hstep := st223o2_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p90 : ((616511285079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 89, stT223o2 (i+1)) + stT223o2 90 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 89
    simpa using h
  have hprev := st223o2_p89
  have hstep := st223o2_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p91 : ((109001684433/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 90, stT223o2 (i+1)) + stT223o2 91 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 90
    simpa using h
  have hprev := st223o2_p90
  have hstep := st223o2_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p92 : ((202808455419/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 91, stT223o2 (i+1)) + stT223o2 92 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 91
    simpa using h
  have hprev := st223o2_p91
  have hstep := st223o2_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p93 : ((861496009137/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 92, stT223o2 (i+1)) + stT223o2 93 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 92
    simpa using h
  have hprev := st223o2_p92
  have hstep := st223o2_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p94 : ((1223389251359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 93, stT223o2 (i+1)) + stT223o2 94 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 93
    simpa using h
  have hprev := st223o2_p93
  have hstep := st223o2_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p95 : ((460692514829/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 94, stT223o2 (i+1)) + stT223o2 95 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 94
    simpa using h
  have hprev := st223o2_p94
  have hstep := st223o2_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p96 : ((635409594893/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 95, stT223o2 (i+1)) + stT223o2 96 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 95
    simpa using h
  have hprev := st223o2_p95
  have hstep := st223o2_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p97 : ((4007994956713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 96, stT223o2 (i+1)) + stT223o2 97 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 96
    simpa using h
  have hprev := st223o2_p96
  have hstep := st223o2_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p98 : ((3822217718483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 97, stT223o2 (i+1)) + stT223o2 98 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 97
    simpa using h
  have hprev := st223o2_p97
  have hstep := st223o2_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p99 : ((2849348974787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 98, stT223o2 (i+1)) + stT223o2 99 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 98
    simpa using h
  have hprev := st223o2_p98
  have hstep := st223o2_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p100 : ((2201966974787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 99, stT223o2 (i+1)) + stT223o2 100 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 99
    simpa using h
  have hprev := st223o2_p99
  have hstep := st223o2_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p101 : ((162145684979/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 100, stT223o2 (i+1)) + stT223o2 101 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 100
    simpa using h
  have hprev := st223o2_p100
  have hstep := st223o2_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p102 : ((1791107241811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 101, stT223o2 (i+1)) + stT223o2 102 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 101
    simpa using h
  have hprev := st223o2_p101
  have hstep := st223o2_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p103 : ((25606691021/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 102, stT223o2 (i+1)) + stT223o2 103 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 102
    simpa using h
  have hprev := st223o2_p102
  have hstep := st223o2_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p104 : ((900868386057/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 103, stT223o2 (i+1)) + stT223o2 104 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 103
    simpa using h
  have hprev := st223o2_p103
  have hstep := st223o2_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p105 : ((2627796025557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 104, stT223o2 (i+1)) + stT223o2 105 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 104
    simpa using h
  have hprev := st223o2_p104
  have hstep := st223o2_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p106 : ((2170395108579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 105, stT223o2 (i+1)) + stT223o2 106 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 105
    simpa using h
  have hprev := st223o2_p105
  have hstep := st223o2_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p107 : ((2681138171891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 106, stT223o2 (i+1)) + stT223o2 107 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 106
    simpa using h
  have hprev := st223o2_p106
  have hstep := st223o2_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p108 : ((3643083138641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 107, stT223o2 (i+1)) + stT223o2 108 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 107
    simpa using h
  have hprev := st223o2_p107
  have hstep := st223o2_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p109 : ((4118996227609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 108, stT223o2 (i+1)) + stT223o2 109 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 108
    simpa using h
  have hprev := st223o2_p108
  have hstep := st223o2_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p110 : ((3663317190649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 109, stT223o2 (i+1)) + stT223o2 110 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 109
    simpa using h
  have hprev := st223o2_p109
  have hstep := st223o2_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p111 : ((2716025235277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 110, stT223o2 (i+1)) + stT223o2 111 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 110
    simpa using h
  have hprev := st223o2_p110
  have hstep := st223o2_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p112 : ((2156009909709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 111, stT223o2 (i+1)) + stT223o2 112 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 111
    simpa using h
  have hprev := st223o2_p111
  have hstep := st223o2_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p113 : ((2484550725389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 112, stT223o2 (i+1)) + stT223o2 113 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 112
    simpa using h
  have hprev := st223o2_p112
  have hstep := st223o2_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p114 : ((3396083949809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 113, stT223o2 (i+1)) + stT223o2 114 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 113
    simpa using h
  have hprev := st223o2_p113
  have hstep := st223o2_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p115 : ((4083270392513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 114, stT223o2 (i+1)) + stT223o2 115 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 114
    simpa using h
  have hprev := st223o2_p114
  have hstep := st223o2_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p116 : ((494576757439/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 115, stT223o2 (i+1)) + stT223o2 116 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 115
    simpa using h
  have hprev := st223o2_p115
  have hstep := st223o2_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p117 : ((3135229127549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 116, stT223o2 (i+1)) + stT223o2 117 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 116
    simpa using h
  have hprev := st223o2_p116
  have hstep := st223o2_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p118 : ((1157636027237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 117, stT223o2 (i+1)) + stT223o2 118 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 117
    simpa using h
  have hprev := st223o2_p117
  have hstep := st223o2_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p119 : ((217113397051/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 118, stT223o2 (i+1)) + stT223o2 119 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 118
    simpa using h
  have hprev := st223o2_p118
  have hstep := st223o2_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p120 : ((70249534813/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 119, stT223o2 (i+1)) + stT223o2 120 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 119
    simpa using h
  have hprev := st223o2_p119
  have hstep := st223o2_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p121 : ((185569297283/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 120, stT223o2 (i+1)) + stT223o2 121 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 120
    simpa using h
  have hprev := st223o2_p120
  have hstep := st223o2_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p122 : ((104095726321/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 121, stT223o2 (i+1)) + stT223o2 122 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 121
    simpa using h
  have hprev := st223o2_p121
  have hstep := st223o2_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p123 : ((191180275921/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 122, stT223o2 (i+1)) + stT223o2 123 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 122
    simpa using h
  have hprev := st223o2_p122
  have hstep := st223o2_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p124 : ((148039058841/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 123, stT223o2 (i+1)) + stT223o2 124 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 123
    simpa using h
  have hprev := st223o2_p123
  have hstep := st223o2_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p125 : ((557481095151/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 124, stT223o2 (i+1)) + stT223o2 125 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 124
    simpa using h
  have hprev := st223o2_p124
  have hstep := st223o2_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p126 : ((135591867159/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 125, stT223o2 (i+1)) + stT223o2 126 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 125
    simpa using h
  have hprev := st223o2_p125
  have hstep := st223o2_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p127 : ((351787825773/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 126, stT223o2 (i+1)) + stT223o2 127 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 126
    simpa using h
  have hprev := st223o2_p126
  have hstep := st223o2_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p128 : ((230754320989/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 127, stT223o2 (i+1)) + stT223o2 128 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 127
    simpa using h
  have hprev := st223o2_p127
  have hstep := st223o2_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p129 : ((522349938103/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 128, stT223o2 (i+1)) + stT223o2 129 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 128
    simpa using h
  have hprev := st223o2_p128
  have hstep := st223o2_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p130 : ((3940421008037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 129, stT223o2 (i+1)) + stT223o2 130 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 129
    simpa using h
  have hprev := st223o2_p129
  have hstep := st223o2_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p131 : ((787583049413/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 130, stT223o2 (i+1)) + stT223o2 131 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 130
    simpa using h
  have hprev := st223o2_p130
  have hstep := st223o2_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p132 : ((2350906883211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 131, stT223o2 (i+1)) + stT223o2 132 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 131
    simpa using h
  have hprev := st223o2_p131
  have hstep := st223o2_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p133 : ((2075999195921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 132, stT223o2 (i+1)) + stT223o2 133 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 132
    simpa using h
  have hprev := st223o2_p132
  have hstep := st223o2_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p134 : ((2499678937181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 133, stT223o2 (i+1)) + stT223o2 134 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 133
    simpa using h
  have hprev := st223o2_p133
  have hstep := st223o2_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p135 : ((133512076829/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 134, stT223o2 (i+1)) + stT223o2 135 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 134
    simpa using h
  have hprev := st223o2_p134
  have hstep := st223o2_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p136 : ((4048493862801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 135, stT223o2 (i+1)) + stT223o2 136 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 135
    simpa using h
  have hprev := st223o2_p135
  have hstep := st223o2_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p137 : ((4184734756163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 136, stT223o2 (i+1)) + stT223o2 137 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 136
    simpa using h
  have hprev := st223o2_p136
  have hstep := st223o2_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p138 : ((229315044487/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 137, stT223o2 (i+1)) + stT223o2 138 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 137
    simpa using h
  have hprev := st223o2_p137
  have hstep := st223o2_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p139 : ((1413207067627/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 138, stT223o2 (i+1)) + stT223o2 139 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 138
    simpa using h
  have hprev := st223o2_p138
  have hstep := st223o2_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p140 : ((2171472255019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 139, stT223o2 (i+1)) + stT223o2 140 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 139
    simpa using h
  have hprev := st223o2_p139
  have hstep := st223o2_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p141 : ((2093275073211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 140, stT223o2 (i+1)) + stT223o2 141 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 140
    simpa using h
  have hprev := st223o2_p140
  have hstep := st223o2_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p142 : ((1315332803043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 141, stT223o2 (i+1)) + stT223o2 142 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 141
    simpa using h
  have hprev := st223o2_p141
  have hstep := st223o2_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p143 : ((346322981377/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 142, stT223o2 (i+1)) + stT223o2 143 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 142
    simpa using h
  have hprev := st223o2_p142
  have hstep := st223o2_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p144 : ((1027302805511/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 143, stT223o2 (i+1)) + stT223o2 144 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 143
    simpa using h
  have hprev := st223o2_p143
  have hstep := st223o2_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p145 : ((1051207423901/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 144, stT223o2 (i+1)) + stT223o2 145 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 144
    simpa using h
  have hprev := st223o2_p144
  have hstep := st223o2_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p146 : ((925838356597/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 145, stT223o2 (i+1)) + stT223o2 146 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 145
    simpa using h
  have hprev := st223o2_p145
  have hstep := st223o2_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p147 : ((144445297811/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 146, stT223o2 (i+1)) + stT223o2 147 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 146
    simpa using h
  have hprev := st223o2_p146
  have hstep := st223o2_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p148 : ((27613827841/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 147, stT223o2 (i+1)) + stT223o2 148 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 147
    simpa using h
  have hprev := st223o2_p147
  have hstep := st223o2_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p149 : ((126751039509/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 148, stT223o2 (i+1)) + stT223o2 149 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 148
    simpa using h
  have hprev := st223o2_p148
  have hstep := st223o2_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p150 : ((38059197109/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 149, stT223o2 (i+1)) + stT223o2 150 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 149
    simpa using h
  have hprev := st223o2_p149
  have hstep := st223o2_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p151 : ((802875072061/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 150, stT223o2 (i+1)) + stT223o2 151 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 150
    simpa using h
  have hprev := st223o2_p150
  have hstep := st223o2_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p152 : ((987264026371/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 151, stT223o2 (i+1)) + stT223o2 152 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 151
    simpa using h
  have hprev := st223o2_p151
  have hstep := st223o2_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p153 : ((1067932175383/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 152, stT223o2 (i+1)) + stT223o2 153 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 152
    simpa using h
  have hprev := st223o2_p152
  have hstep := st223o2_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p154 : ((1005360019433/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 153, stT223o2 (i+1)) + stT223o2 154 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 153
    simpa using h
  have hprev := st223o2_p153
  have hstep := st223o2_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p155 : ((832433982413/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 154, stT223o2 (i+1)) + stT223o2 155 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 154
    simpa using h
  have hprev := st223o2_p154
  have hstep := st223o2_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p156 : ((635631620767/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 155, stT223o2 (i+1)) + stT223o2 156 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 155
    simpa using h
  have hprev := st223o2_p155
  have hstep := st223o2_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p157 : ((1021997526911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 156, stT223o2 (i+1)) + stT223o2 157 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 156
    simpa using h
  have hprev := st223o2_p156
  have hstep := st223o2_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p158 : ((2070449710743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 157, stT223o2 (i+1)) + stT223o2 158 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 157
    simpa using h
  have hprev := st223o2_p157
  have hstep := st223o2_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p159 : ((2603267369501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 158, stT223o2 (i+1)) + stT223o2 159 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 158
    simpa using h
  have hprev := st223o2_p158
  have hstep := st223o2_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p160 : ((3386608987703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 159, stT223o2 (i+1)) + stT223o2 160 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 159
    simpa using h
  have hprev := st223o2_p159
  have hstep := st223o2_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p161 : ((4054402962663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 160, stT223o2 (i+1)) + stT223o2 161 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 160
    simpa using h
  have hprev := st223o2_p160
  have hstep := st223o2_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p162 : ((4301986124891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 161, stT223o2 (i+1)) + stT223o2 162 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 161
    simpa using h
  have hprev := st223o2_p161
  have hstep := st223o2_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p163 : ((1005495908207/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 162, stT223o2 (i+1)) + stT223o2 163 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 162
    simpa using h
  have hprev := st223o2_p162
  have hstep := st223o2_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p164 : ((3345583191993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 163, stT223o2 (i+1)) + stT223o2 164 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 163
    simpa using h
  have hprev := st223o2_p163
  have hstep := st223o2_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p165 : ((322039746079/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 164, stT223o2 (i+1)) + stT223o2 165 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 164
    simpa using h
  have hprev := st223o2_p164
  have hstep := st223o2_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p166 : ((2051451287939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 165, stT223o2 (i+1)) + stT223o2 166 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 165
    simpa using h
  have hprev := st223o2_p165
  have hstep := st223o2_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p167 : ((1995041839811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 166, stT223o2 (i+1)) + stT223o2 167 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 166
    simpa using h
  have hprev := st223o2_p166
  have hstep := st223o2_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p168 : ((97040550539/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 167, stT223o2 (i+1)) + stT223o2 168 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 167
    simpa using h
  have hprev := st223o2_p167
  have hstep := st223o2_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p169 : ((631408606489/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 168, stT223o2 (i+1)) + stT223o2 169 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 168
    simpa using h
  have hprev := st223o2_p168
  have hstep := st223o2_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p170 : ((3879677280209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 169, stT223o2 (i+1)) + stT223o2 170 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 169
    simpa using h
  have hprev := st223o2_p169
  have hstep := st223o2_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p171 : ((4295730299349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 170, stT223o2 (i+1)) + stT223o2 171 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 170
    simpa using h
  have hprev := st223o2_p170
  have hstep := st223o2_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p172 : ((4238695822949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 171, stT223o2 (i+1)) + stT223o2 172 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 171
    simpa using h
  have hprev := st223o2_p171
  have hstep := st223o2_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p173 : ((3736652367139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 172, stT223o2 (i+1)) + stT223o2 173 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 172
    simpa using h
  have hprev := st223o2_p172
  have hstep := st223o2_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p174 : ((374336377569/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 173, stT223o2 (i+1)) + stT223o2 174 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 173
    simpa using h
  have hprev := st223o2_p173
  have hstep := st223o2_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p175 : ((1154089490311/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 174, stT223o2 (i+1)) + stT223o2 175 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 174
    simpa using h
  have hprev := st223o2_p174
  have hstep := st223o2_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p176 : ((77779435583/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 175, stT223o2 (i+1)) + stT223o2 176 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 175
    simpa using h
  have hprev := st223o2_p175
  have hstep := st223o2_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p177 : ((2040610889931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 176, stT223o2 (i+1)) + stT223o2 177 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 176
    simpa using h
  have hprev := st223o2_p176
  have hstep := st223o2_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p178 : ((2555014015231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 177, stT223o2 (i+1)) + stT223o2 178 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 177
    simpa using h
  have hprev := st223o2_p177
  have hstep := st223o2_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p179 : ((1644502450943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 178, stT223o2 (i+1)) + stT223o2 179 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 178
    simpa using h
  have hprev := st223o2_p178
  have hstep := st223o2_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p180 : ((3966007121611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 179, stT223o2 (i+1)) + stT223o2 180 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 179
    simpa using h
  have hprev := st223o2_p179
  have hstep := st223o2_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p181 : ((867263387141/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 180, stT223o2 (i+1)) + stT223o2 181 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 180
    simpa using h
  have hprev := st223o2_p180
  have hstep := st223o2_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p182 : ((853526097391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 181, stT223o2 (i+1)) + stT223o2 182 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 181
    simpa using h
  have hprev := st223o2_p181
  have hstep := st223o2_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p183 : ((3789281409199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 182, stT223o2 (i+1)) + stT223o2 183 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 182
    simpa using h
  have hprev := st223o2_p182
  have hstep := st223o2_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p184 : ((3076709704609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 183, stT223o2 (i+1)) + stT223o2 184 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 183
    simpa using h
  have hprev := st223o2_p183
  have hstep := st223o2_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p185 : ((9315428159/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 184, stT223o2 (i+1)) + stT223o2 185 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 184
    simpa using h
  have hprev := st223o2_p184
  have hstep := st223o2_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p186 : ((61118588029/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 185, stT223o2 (i+1)) + stT223o2 186 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 185
    simpa using h
  have hprev := st223o2_p185
  have hstep := st223o2_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p187 : ((484007492571/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 186, stT223o2 (i+1)) + stT223o2 187 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 186
    simpa using h
  have hprev := st223o2_p186
  have hstep := st223o2_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p188 : ((291017327547/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 187, stT223o2 (i+1)) + stT223o2 188 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 187
    simpa using h
  have hprev := st223o2_p187
  have hstep := st223o2_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p189 : ((374343081639/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 188, stT223o2 (i+1)) + stT223o2 189 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 188
    simpa using h
  have hprev := st223o2_p188
  have hstep := st223o2_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p190 : ((115902364357/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 189, stT223o2 (i+1)) + stT223o2 190 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 189
    simpa using h
  have hprev := st223o2_p189
  have hstep := st223o2_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p191 : ((423226495301/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 190, stT223o2 (i+1)) + stT223o2 191 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 190
    simpa using h
  have hprev := st223o2_p190
  have hstep := st223o2_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p192 : ((4394262755587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 191, stT223o2 (i+1)) + stT223o2 192 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 191
    simpa using h
  have hprev := st223o2_p191
  have hstep := st223o2_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p193 : ((4145531056603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 192, stT223o2 (i+1)) + stT223o2 193 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 192
    simpa using h
  have hprev := st223o2_p192
  have hstep := st223o2_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p194 : ((714078840911/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 193, stT223o2 (i+1)) + stT223o2 194 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 193
    simpa using h
  have hprev := st223o2_p193
  have hstep := st223o2_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p195 : ((285592412071/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 194, stT223o2 (i+1)) + stT223o2 195 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 194
    simpa using h
  have hprev := st223o2_p194
  have hstep := st223o2_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p196 : ((557415431837/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 195, stT223o2 (i+1)) + stT223o2 196 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 195
    simpa using h
  have hprev := st223o2_p195
  have hstep := st223o2_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p197 : ((943536448441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 196, stT223o2 (i+1)) + stT223o2 197 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 196
    simpa using h
  have hprev := st223o2_p196
  have hstep := st223o2_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p198 : ((1931777530327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 197, stT223o2 (i+1)) + stT223o2 198 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 197
    simpa using h
  have hprev := st223o2_p197
  have hstep := st223o2_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p199 : ((2346339645699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 198, stT223o2 (i+1)) + stT223o2 199 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 198
    simpa using h
  have hprev := st223o2_p198
  have hstep := st223o2_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p200 : ((3001066768749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 199, stT223o2 (i+1)) + stT223o2 200 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 199
    simpa using h
  have hprev := st223o2_p199
  have hstep := st223o2_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p201 : ((3696336620769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 200, stT223o2 (i+1)) + stT223o2 201 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 200
    simpa using h
  have hprev := st223o2_p200
  have hstep := st223o2_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p202 : ((4224213084407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 201, stT223o2 (i+1)) + stT223o2 202 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 201
    simpa using h
  have hprev := st223o2_p201
  have hstep := st223o2_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p203 : ((4430186419961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 202, stT223o2 (i+1)) + stT223o2 203 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 202
    simpa using h
  have hprev := st223o2_p202
  have hstep := st223o2_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p204 : ((2128463713839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 203, stT223o2 (i+1)) + stT223o2 204 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 203
    simpa using h
  have hprev := st223o2_p203
  have hstep := st223o2_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p205 : ((751637944781/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 204, stT223o2 (i+1)) + stT223o2 205 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 204
    simpa using h
  have hprev := st223o2_p204
  have hstep := st223o2_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p206 : ((3080243852949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 205, stT223o2 (i+1)) + stT223o2 206 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 205
    simpa using h
  have hprev := st223o2_p205
  have hstep := st223o2_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p207 : ((12088264731/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 206, stT223o2 (i+1)) + stT223o2 207 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 206
    simpa using h
  have hprev := st223o2_p206
  have hstep := st223o2_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p208 : ((244631882099/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 207, stT223o2 (i+1)) + stT223o2 208 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 207
    simpa using h
  have hprev := st223o2_p207
  have hstep := st223o2_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p209 : ((456308386453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 208, stT223o2 (i+1)) + stT223o2 209 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 208
    simpa using h
  have hprev := st223o2_p208
  have hstep := st223o2_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p210 : ((1027834855761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 209, stT223o2 (i+1)) + stT223o2 210 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 209
    simpa using h
  have hprev := st223o2_p209
  have hstep := st223o2_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p211 : ((1290958921641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 210, stT223o2 (i+1)) + stT223o2 211 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 210
    simpa using h
  have hprev := st223o2_p210
  have hstep := st223o2_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p212 : ((1629193796997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 211, stT223o2 (i+1)) + stT223o2 212 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 211
    simpa using h
  have hprev := st223o2_p211
  have hstep := st223o2_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p213 : ((1950845025777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 212, stT223o2 (i+1)) + stT223o2 213 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 212
    simpa using h
  have hprev := st223o2_p212
  have hstep := st223o2_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p214 : ((4340583750049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 213, stT223o2 (i+1)) + stT223o2 214 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 213
    simpa using h
  have hprev := st223o2_p213
  have hstep := st223o2_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p215 : ((4460912043433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 214, stT223o2 (i+1)) + stT223o2 215 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 214
    simpa using h
  have hprev := st223o2_p214
  have hstep := st223o2_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p216 : ((4233976964083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 215, stT223o2 (i+1)) + stT223o2 216 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 215
    simpa using h
  have hprev := st223o2_p215
  have hstep := st223o2_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p217 : ((3721706950183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 216, stT223o2 (i+1)) + stT223o2 217 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 216
    simpa using h
  have hprev := st223o2_p216
  have hstep := st223o2_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p218 : ((3058315472473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 217, stT223o2 (i+1)) + stT223o2 218 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 217
    simpa using h
  have hprev := st223o2_p217
  have hstep := st223o2_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p219 : ((2414168223973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 218, stT223o2 (i+1)) + stT223o2 219 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 218
    simpa using h
  have hprev := st223o2_p218
  have hstep := st223o2_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p220 : ((1951780963773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 219, stT223o2 (i+1)) + stT223o2 220 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 219
    simpa using h
  have hprev := st223o2_p219
  have hstep := st223o2_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p221 : ((44633015763/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 220, stT223o2 (i+1)) + stT223o2 221 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 220
    simpa using h
  have hprev := st223o2_p220
  have hstep := st223o2_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p222 : ((488382611333/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 221, stT223o2 (i+1)) + stT223o2 222 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 221
    simpa using h
  have hprev := st223o2_p221
  have hstep := st223o2_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p223 : ((1206079156577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 222, stT223o2 (i+1)) + stT223o2 223 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 222
    simpa using h
  have hprev := st223o2_p222
  have hstep := st223o2_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p224 : ((609380331739/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 223, stT223o2 (i+1)) + stT223o2 224 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 223
    simpa using h
  have hprev := st223o2_p223
  have hstep := st223o2_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p225 : ((3702853002743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 224, stT223o2 (i+1)) + stT223o2 225 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 224
    simpa using h
  have hprev := st223o2_p224
  have hstep := st223o2_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p226 : ((4222675040903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 225, stT223o2 (i+1)) + stT223o2 226 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 225
    simpa using h
  have hprev := st223o2_p225
  have hstep := st223o2_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p227 : ((4484047830857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 226, stT223o2 (i+1)) + stT223o2 227 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 226
    simpa using h
  have hprev := st223o2_p226
  have hstep := st223o2_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p228 : ((276724637811/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 227, stT223o2 (i+1)) + stT223o2 228 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 227
    simpa using h
  have hprev := st223o2_p227
  have hstep := st223o2_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p229 : ((2034574399041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 228, stT223o2 (i+1)) + stT223o2 229 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 228
    simpa using h
  have hprev := st223o2_p228
  have hstep := st223o2_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p230 : ((873547746259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 229, stT223o2 (i+1)) + stT223o2 230 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 229
    simpa using h
  have hprev := st223o2_p229
  have hstep := st223o2_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p231 : ((709115836667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 230, stT223o2 (i+1)) + stT223o2 231 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 230
    simpa using h
  have hprev := st223o2_p230
  have hstep := st223o2_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p232 : ((449262348353/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 231, stT223o2 (i+1)) + stT223o2 232 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 231
    simpa using h
  have hprev := st223o2_p231
  have hstep := st223o2_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p233 : ((371266798643/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 232, stT223o2 (i+1)) + stT223o2 233 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 232
    simpa using h
  have hprev := st223o2_p232
  have hstep := st223o2_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p234 : ((876066413489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 233, stT223o2 (i+1)) + stT223o2 234 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 233
    simpa using h
  have hprev := st223o2_p233
  have hstep := st223o2_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p235 : ((977240855469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 234, stT223o2 (i+1)) + stT223o2 235 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 234
    simpa using h
  have hprev := st223o2_p234
  have hstep := st223o2_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p236 : ((241635121481/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 235, stT223o2 (i+1)) + stT223o2 236 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 235
    simpa using h
  have hprev := st223o2_p235
  have hstep := st223o2_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p237 : ((758710234109/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 236, stT223o2 (i+1)) + stT223o2 237 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 236
    simpa using h
  have hprev := st223o2_p236
  have hstep := st223o2_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p238 : ((183741495401/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 237, stT223o2 (i+1)) + stT223o2 238 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 237
    simpa using h
  have hprev := st223o2_p237
  have hstep := st223o2_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p239 : ((262423528857/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 238, stT223o2 (i+1)) + stT223o2 239 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 238
    simpa using h
  have hprev := st223o2_p238
  have hstep := st223o2_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p240 : ((224803457101/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 239, stT223o2 (i+1)) + stT223o2 240 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 239
    simpa using h
  have hprev := st223o2_p239
  have hstep := st223o2_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p241 : ((1126435769207/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 240, stT223o2 (i+1)) + stT223o2 241 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 240
    simpa using h
  have hprev := st223o2_p240
  have hstep := st223o2_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p242 : ((4228056176153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 241, stT223o2 (i+1)) + stT223o2 242 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 241
    simpa using h
  have hprev := st223o2_p241
  have hstep := st223o2_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p243 : ((3722967797799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 242, stT223o2 (i+1)) + stT223o2 243 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 242
    simpa using h
  have hprev := st223o2_p242
  have hstep := st223o2_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p244 : ((3096347037579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 243, stT223o2 (i+1)) + stT223o2 244 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 243
    simpa using h
  have hprev := st223o2_p243
  have hstep := st223o2_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p245 : ((1238615571033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 244, stT223o2 (i+1)) + stT223o2 245 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 244
    simpa using h
  have hprev := st223o2_p244
  have hstep := st223o2_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p246 : ((1991094618991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 245, stT223o2 (i+1)) + stT223o2 246 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 245
    simpa using h
  have hprev := st223o2_p245
  have hstep := st223o2_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p247 : ((433670645209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 246, stT223o2 (i+1)) + stT223o2 247 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 246
    simpa using h
  have hprev := st223o2_p246
  have hstep := st223o2_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p248 : ((439342623959/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 247, stT223o2 (i+1)) + stT223o2 248 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 247
    simpa using h
  have hprev := st223o2_p247
  have hstep := st223o2_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p249 : ((256561732683/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 248, stT223o2 (i+1)) + stT223o2 249 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 248
    simpa using h
  have hprev := st223o2_p248
  have hstep := st223o2_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_p250 : ((1279984714457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT223o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT223o2 (i+1))
      = (∑ i ∈ Finset.range 249, stT223o2 (i+1)) + stT223o2 250 := by
    have h := Finset.sum_range_succ (fun i => stT223o2 (i+1)) 249
    simpa using h
  have hprev := st223o2_p249
  have hstep := st223o2_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st223o2_s250 :
    |Real.sin (((223 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))
      - ((-149183/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log ((250 : ℕ)) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((250 : ℕ)) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact sinMulShift_eval (r := -1598557/10000000) (δ := 921/100000000) (ψ := 106031/200000) 223 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 223/2`** (evaluated boundary). -/
theorem station_223o2_sign : hardyG (((((223:ℕ)):ℝ)/2)) < 0 := by
  have hcore := phase_station_lower_half_eval 223 250 (by norm_num) (by norm_num)
    ((106031/200000 : ℚ) : ℝ)
  have hchain := st223o2_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT223o2 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((223 : ℕ) : ℝ) * (Real.log ((i+1 : ℕ)) / 2)
              - ((106031/200000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st223o2_c250
  have hsinb := abs_le.mp st223o2_s250
  have hbdy_lo : ((4182348893909/49730000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((223 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ))) / 2
          - ((((223:ℕ)):ℝ)/2)
            * Real.sin (((223 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((106031/200000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((223:ℕ)):ℝ)/2) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((223:ℝ) * (Real.log (250:ℝ) / 2) - ((106031/200000 : ℚ) : ℝ))) / 2
        - ((223:ℝ)/2) * Real.sin ((223:ℝ) * (Real.log (250:ℝ) / 2) - ((106031/200000 : ℚ) : ℝ))
        ≥ ((33064399/500000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((223:ℝ)/2) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((33064399/500000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((33064399/500000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((33064399/500000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((223:ℕ)):ℝ)/2)+1) * (((((223:ℕ)):ℝ)/2)+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((30242701951/100000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1279984714457/5000000000000 : ℚ) : ℝ) + ((4182348893909/49730000000000 : ℚ) : ℝ)
      - ((30242701951/100000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((106031/200000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line (((((223:ℕ)):ℝ)/2)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((106031/200000 : ℚ) : ℝ)
        * (riemannZeta (line (((((223:ℕ)):ℝ)/2)))).re
      - Real.sin ((106031/200000 : ℚ) : ℝ)
        * (riemannZeta (line (((((223:ℕ)):ℝ)/2)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((((223:ℕ)):ℝ)/2))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((((223:ℕ)):ℝ)/2))
      = ((((((223:ℕ)):ℝ)/2)) * (Real.log (((((223:ℕ)):ℝ)/2)) - Real.log 2
          - Real.log Real.pi) - (((((223:ℕ)):ℝ)/2))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM : ((9428049/2000000 : ℚ) : ℝ) ≤ Real.log (((((223:ℕ)):ℝ)/2))
      ∧ Real.log (((((223:ℕ)):ℝ)/2)) ≤ ((47140247/10000000 : ℚ) : ℝ) := by
    have hsplit : Real.log (((((223:ℕ)):ℝ)/2))
        = Real.log ((((223:ℕ)):ℝ)) - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    have hM := log_br_223
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
  have hθwin : |(((106031/200000 : ℚ) : ℝ) + ((17:ℤ)) * (2*Real.pi) - Real.pi) - theta (((((223:ℕ)):ℝ)/2))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((((223:ℕ)):ℝ)/2)))
    (φ := ((106031/200000 : ℚ) : ℝ) + ((17:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((106031/200000 : ℚ) : ℝ) + ((17:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((106031/200000 : ℚ)) : ℝ) - Real.pi) + ((17:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((106031/200000 : ℚ)) : ℝ) - Real.pi) 17).1,
    (cos_sin_shift ((((106031/200000 : ℚ)) : ℝ) - Real.pi) 17).2]
  exact cos_sin_flip ((106031/200000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_223o2_sign
end AxiomAudit
