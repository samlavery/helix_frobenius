import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationHalfEval

/-!
# Station `t = 395/2` (rung-199.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT395o2 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((395 : ℕ) : ℝ) * (Real.log ((n : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))

theorem st395o2_c1 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((1699/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((0 : ℚ) : ℝ) ≤ Real.log ((1 : ℕ)) / 2 := by
    have h := (log_br_1).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((1 : ℕ)) / 2 ≤ ((0 : ℚ) : ℝ) := by
    have h := (log_br_1).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 694699/5000000) (δ := 201/1000000000) (ψ := -555759/1000000) 395 0
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t1 : ((16989/20000 : ℚ) : ℝ) ≤ stT395o2 1 := by
  have hc : ((16989/20000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16989/20000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((16989/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c2 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((71249/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log ((2 : ℕ)) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((2 : ℕ)) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1944389/10000000) (δ := 9909/1000000000) (ψ := -555759/1000000) 395 22
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t2 : ((125942774337/250000000000 : ℚ) : ℝ) ≤ stT395o2 2 := by
  have hc : ((17811/25000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125942774337/250000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((17811/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c3 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-144721/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log ((3 : ℕ)) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((3 : ℕ)) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2974759/5000000) (δ := 10053/1000000000) (ψ := -555759/1000000) 395 35
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t3 : ((-835604862693/2000000000000 : ℚ) : ℝ) ≤ stT395o2 3 := by
  have hc : ((-144731/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-835604862693/2000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-144731/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c4 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-257267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log ((4 : ℕ)) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((4 : ℕ)) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5278151/10000000) (δ := 4943/500000000) (ψ := -555759/1000000) 395 44
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t4 : ((-321615064323/1250000000000 : ℚ) : ℝ) ≤ stT395o2 4 := by
  have hc : ((-64323/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321615064323/1250000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-64323/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c5 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-109169/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log ((5 : ℕ)) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((5 : ℕ)) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5056741/10000000) (δ := 5009/500000000) (ψ := -555759/1000000) 395 51
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t5 : ((-122068629171/625000000000 : ℚ) : ℝ) ≤ stT395o2 5 := by
  have hc : ((-218363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122068629171/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-218363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c6 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-210243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log ((6 : ℕ)) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((6 : ℕ)) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6424683/10000000) (δ := 619/62500000) (ψ := -555759/1000000) 395 56
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t6 : ((-1716729008813/5000000000000 : ℚ) : ℝ) ≤ stT395o2 6 := by
  have hc : ((-420511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1716729008813/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-420511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c7 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-2791/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log ((7 : ℕ)) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((7 : ℕ)) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 159871/400000) (δ := 9989/1000000000) (ψ := -555759/1000000) 395 61
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t7 : ((-528394371/50000000000 : ℚ) : ℝ) ≤ stT395o2 7 := by
  have hc : ((-699/25000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-528394371/50000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-699/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c8 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-477197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log ((8 : ℕ)) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((8 : ℕ)) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 141921/200000) (δ := 2007/200000000) (ψ := -555759/1000000) 395 65
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t8 : ((-421808651637/1250000000000 : ℚ) : ℝ) ≤ stT395o2 8 := by
  have hc : ((-238611/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-421808651637/1250000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-238611/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c9 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((113419/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log ((9 : ℕ)) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((9 : ℕ)) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1209777/5000000) (δ := 10047/1000000000) (ψ := -555759/1000000) 395 69
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t9 : ((378029962197/2000000000000 : ℚ) : ℝ) ≤ stT395o2 9 := by
  have hc : ((113409/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((378029962197/2000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((113409/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c10 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-30533/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log ((10 : ℕ)) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((10 : ℕ)) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7317411/10000000) (δ := 5009/500000000) (ψ := -555759/1000000) 395 72
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t10 : ((-772470201867/2500000000000 : ℚ) : ℝ) ≤ stT395o2 10 := by
  have hc : ((-488553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-772470201867/2500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-488553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c11 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-485619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log ((11 : ℕ)) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((11 : ℕ)) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1813233/2500000) (δ := 9913/1000000000) (ψ := -555759/1000000) 395 75
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t11 : ((-183034002927/625000000000 : ℚ) : ℝ) ≤ stT395o2 11 := by
  have hc : ((-121411/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183034002927/625000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-121411/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c12 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((328229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log ((12 : ℕ)) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((12 : ℕ)) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3090921/10000000) (δ := 9891/1000000000) (ψ := -555759/1000000) 395 78
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t12 : ((947371056429/10000000000000 : ℚ) : ℝ) ≤ stT395o2 12 := by
  have hc : ((328179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((947371056429/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((328179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c13 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-23183/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log ((13 : ℕ)) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((13 : ℕ)) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2255943/5000000) (δ := 501/50000000) (ψ := -555759/1000000) 395 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t13 : ((-16077985297/250000000000 : ℚ) : ℝ) ≤ stT395o2 13 := by
  have hc : ((-5797/25000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16077985297/250000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-5797/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c14 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((965039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log ((14 : ℕ)) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((14 : ℕ)) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 663013/10000000) (δ := 9947/1000000000) (ψ := -555759/1000000) 395 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t14 : ((644760295317/2500000000000 : ℚ) : ℝ) ≤ stT395o2 14 := by
  have hc : ((964989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((644760295317/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((964989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c15 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((121697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log ((15 : ℕ)) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((15 : ℕ)) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3312331/10000000) (δ := 2503/250000000) (ψ := -555759/1000000) 395 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t15 : ((9817363873/156250000000 : ℚ) : ℝ) ≤ stT395o2 15 := by
  have hc : ((15209/62500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9817363873/156250000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((15209/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c16 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((65833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log ((16 : ℕ)) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((16 : ℕ)) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3762289/10000000) (δ := 2519/250000000) (ψ := -555759/1000000) 395 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t16 : ((65783/4000000 : ℚ) : ℝ) ≤ stT395o2 16 := by
  have hc : ((65783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65783/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((65783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c17 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((306121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log ((17 : ℕ)) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((17 : ℕ)) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1139879/5000000) (δ := 9963/1000000000) (ψ := -555759/1000000) 395 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t17 : ((11599871409/78125000000 : ℚ) : ℝ) ≤ stT395o2 17 := by
  have hc : ((19131/31250 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11599871409/78125000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((19131/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c18 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((23347/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log ((18 : ℕ)) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((18 : ℕ)) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -28569/312500) (δ := 2001/200000000) (ψ := -555759/1000000) 395 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t18 : ((110052892713/500000000000 : ℚ) : ℝ) ≤ stT395o2 18 := by
  have hc : ((93383/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110052892713/500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((93383/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c19 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-78889/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log ((19 : ℕ)) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((19 : ℕ)) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1126891/2000000) (δ := 4967/500000000) (ψ := -555759/1000000) 395 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t19 : ((-361996337899/2500000000000 : ℚ) : ℝ) ≤ stT395o2 19 := by
  have hc : ((-315581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361996337899/2500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-315581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c20 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-22661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log ((20 : ℕ)) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((20 : ℕ)) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3983649/10000000) (δ := 1247/125000000) (ψ := -555759/1000000) 395 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t20 : ((-12695835087/2500000000000 : ℚ) : ℝ) ≤ stT395o2 20 := by
  have hc : ((-22711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12695835087/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-22711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c21 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((231821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log ((21 : ℕ)) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((21 : ℕ)) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3342117/10000000) (δ := 5031/500000000) (ψ := -555759/1000000) 395 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t21 : ((252882788619/5000000000000 : ℚ) : ℝ) ≤ stT395o2 21 := by
  have hc : ((231771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252882788619/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((231771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c22 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((391/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log ((22 : ℕ)) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((22 : ℕ)) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 391917/1000000) (δ := 1991/200000000) (ψ := -555759/1000000) 395 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t22 : ((3281158773/5000000000000 : ℚ) : ℝ) ≤ stT395o2 22 := by
  have hc : ((1539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3281158773/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((1539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c23 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-151033/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log ((23 : ℕ)) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((23 : ℕ)) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -138717/250000) (δ := 1239/125000000) (ψ := -555759/1000000) 395 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t23 : ((-125980707639/1000000000000 : ℚ) : ℝ) ≤ stT395o2 23 := by
  have hc : ((-302091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125980707639/1000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-302091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c24 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((497643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log ((24 : ℕ)) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((24 : ℕ)) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -242841/10000000) (δ := 4967/500000000) (ψ := -555759/1000000) 395 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t24 : ((507879131969/2500000000000 : ℚ) : ℝ) ≤ stT395o2 24 := by
  have hc : ((248809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((507879131969/2500000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((248809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c25 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-55499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log ((25 : ℕ)) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((25 : ℕ)) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2102529/5000000) (δ := 5013/500000000) (ψ := -555759/1000000) 395 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t25 : ((-27762013881/1250000000000 : ℚ) : ℝ) ≤ stT395o2 25 := by
  have hc : ((-13881/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27762013881/1250000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-13881/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c26 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-499997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log ((26 : ℕ)) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((26 : ℕ)) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -490353/625000) (δ := 5031/500000000) (ψ := -555759/1000000) 395 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t26 : ((-245156036391/1250000000000 : ℚ) : ℝ) ≤ stT395o2 26 := by
  have hc : ((-250011/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245156036391/1250000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-250011/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c27 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-386597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log ((27 : ℕ)) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((27 : ℕ)) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2459669/5000000) (δ := 2001/200000000) (ψ := -555759/1000000) 395 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t27 : ((-744102538147/10000000000000 : ℚ) : ℝ) ≤ stT395o2 27 := by
  have hc : ((-386647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-744102538147/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-386647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c28 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((96323/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log ((28 : ℕ)) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((28 : ℕ)) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2670749/10000000) (δ := 1981/200000000) (ψ := -555759/1000000) 395 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t28 : ((91007213143/1000000000000 : ℚ) : ℝ) ≤ stT395o2 28 := by
  have hc : ((96313/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91007213143/1000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((96313/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c29 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((9127/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log ((29 : ℕ)) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((29 : ℕ)) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1052383/10000000) (δ := 989/100000000) (ψ := -555759/1000000) 395 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t29 : ((33894963109/200000000000 : ℚ) : ℝ) ≤ stT395o2 29 := by
  have hc : ((18253/20000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33894963109/200000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((18253/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c30 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((999963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log ((30 : ℕ)) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((30 : ℕ)) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -21481/10000000) (δ := 10033/1000000000) (ψ := -555759/1000000) 395 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t30 : ((1825582160533/10000000000000 : ℚ) : ℝ) ≤ stT395o2 30 := by
  have hc : ((999913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1825582160533/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((999913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c31 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((491539/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log ((31 : ℕ)) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((31 : ℕ)) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 460569/10000000) (δ := 1247/125000000) (ψ := -555759/1000000) 395 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t31 : ((441392597121/2500000000000 : ℚ) : ℝ) ≤ stT395o2 31 := by
  have hc : ((245757/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((441392597121/2500000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((245757/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c32 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((197069/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log ((32 : ℕ)) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((32 : ℕ)) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 428527/10000000) (δ := 5017/500000000) (ψ := -555759/1000000) 395 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t32 : ((174177100097/1000000000000 : ℚ) : ℝ) ≤ stT395o2 32 := by
  have hc : ((197059/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174177100097/1000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((197059/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c33 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((999409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log ((33 : ℕ)) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((33 : ℕ)) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -85959/10000000) (δ := 9941/1000000000) (ψ := -555759/1000000) 395 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t33 : ((217457520323/1250000000000 : ℚ) : ℝ) ≤ stT395o2 33 := by
  have hc : ((999359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217457520323/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((999359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c34 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((182487/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log ((34 : ℕ)) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((34 : ℕ)) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -263501/2500000) (δ := 2001/200000000) (ψ := -555759/1000000) 395 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t34 : ((62589063569/400000000000 : ℚ) : ℝ) ≤ stT395o2 34 := by
  have hc : ((182477/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62589063569/400000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((182477/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c35 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((278613/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log ((35 : ℕ)) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((35 : ℕ)) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2449389/10000000) (δ := 9947/1000000000) (ψ := -555759/1000000) 395 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t35 : ((29431220319/312500000000 : ℚ) : ℝ) ≤ stT395o2 35 := by
  have hc : ((69647/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29431220319/312500000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((69647/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c36 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-128039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log ((36 : ℕ)) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((36 : ℕ)) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -424797/1000000) (δ := 9963/1000000000) (ψ := -555759/1000000) 395 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t36 : ((-213481709363/10000000000000 : ℚ) : ℝ) ≤ stT395o2 36 := by
  have hc : ((-128089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213481709363/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-128089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c37 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-841619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log ((37 : ℕ)) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((37 : ℕ)) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6427677/10000000) (δ := 997/100000000) (ψ := -555759/1000000) 395 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t37 : ((-138369541931/1000000000000 : ℚ) : ℝ) ≤ stT395o2 37 := by
  have hc : ((-841669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138369541931/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-841669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c38 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-112789/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log ((38 : ℕ)) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((38 : ℕ)) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6739747/10000000) (δ := 1007/100000000) (ψ := -555759/1000000) 395 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t38 : ((-146382517183/1000000000000 : ℚ) : ℝ) ≤ stT395o2 38 := by
  have hc : ((-451181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146382517183/1000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-451181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c39 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((13959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log ((39 : ℕ)) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((39 : ℕ)) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1928593/5000000) (δ := 5013/500000000) (ψ := -555759/1000000) 395 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t39 : ((11156124727/2500000000000 : ℚ) : ℝ) ≤ stT395o2 39 := by
  have hc : ((6967/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11156124727/2500000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((6967/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c40 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((483201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log ((40 : ℕ)) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((40 : ℕ)) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 649887/10000000) (δ := 4967/500000000) (ψ := -555759/1000000) 395 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t40 : ((47747995893/312500000000 : ℚ) : ℝ) ≤ stT395o2 40 := by
  have hc : ((60397/62500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47747995893/312500000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((60397/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c41 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((102933/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log ((41 : ℕ)) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((41 : ℕ)) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -573221/2000000) (δ := 4971/500000000) (ψ := -555759/1000000) 395 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t41 : ((321469505817/5000000000000 : ℚ) : ℝ) ≤ stT395o2 41 := by
  have hc : ((205841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((321469505817/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((205841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c42 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-178201/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log ((42 : ℕ)) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((42 : ℕ)) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3337939/5000000) (δ := 10049/1000000000) (ψ := -555759/1000000) 395 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t42 : ((-137492816087/1000000000000 : ℚ) : ℝ) ≤ stT395o2 42 := by
  have hc : ((-178211/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137492816087/1000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-178211/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c43 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-395053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log ((43 : ℕ)) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((43 : ℕ)) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2471153/5000000) (δ := 9899/1000000000) (ψ := -555759/1000000) 395 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t43 : ((-301263271779/5000000000000 : ℚ) : ℝ) ≤ stT395o2 43 := by
  have hc : ((-395103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-301263271779/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-395103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c44 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((972709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log ((44 : ℕ)) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((44 : ℕ)) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 9147/156250) (δ := 9997/1000000000) (ψ := -555759/1000000) 395 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t44 : ((366584477851/2500000000000 : ℚ) : ℝ) ≤ stT395o2 44 := by
  have hc : ((972659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((366584477851/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((972659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c45 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-39837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log ((45 : ℕ)) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((45 : ℕ)) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -402661/1000000) (δ := 989/100000000) (ψ := -555759/1000000) 395 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t45 : ((-7432503693/1250000000000 : ℚ) : ℝ) ≤ stT395o2 45 := by
  have hc : ((-39887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7432503693/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-39887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c46 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-11457/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log ((46 : ℕ)) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((46 : ℕ)) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 53324/78125) (δ := 9913/1000000000) (ψ := -555759/1000000) 395 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t46 : ((-6757340581/50000000000 : ℚ) : ℝ) ≤ stT395o2 46 := by
  have hc : ((-91661/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6757340581/50000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-91661/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c47 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((6147/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log ((47 : ℕ)) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((47 : ℕ)) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 434061/2500000) (δ := 9983/1000000000) (ψ := -555759/1000000) 395 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t47 : ((44828659717/400000000000 : ℚ) : ℝ) ≤ stT395o2 47 := by
  have hc : ((30733/40000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44828659717/400000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((30733/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c48 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((139697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log ((48 : ℕ)) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((48 : ℕ)) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3576603/10000000) (δ := 1247/125000000) (ψ := -555759/1000000) 395 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t48 : ((1612503909/80000000000 : ℚ) : ℝ) ≤ stT395o2 48 := by
  have hc : ((139647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1612503909/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((139647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c49 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-87761/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log ((49 : ℕ)) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((49 : ℕ)) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6604127/10000000) (δ := 1247/125000000) (ψ := -555759/1000000) 395 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t49 : ((-15672506269/125000000000 : ℚ) : ℝ) ≤ stT395o2 49 := by
  have hc : ((-43883/50000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15672506269/125000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-43883/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c50 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((23497/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log ((50 : ℕ)) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((50 : ℕ)) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6807/78125) (δ := 2517/250000000) (ψ := -555759/1000000) 395 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t50 : ((132911980379/1000000000000 : ℚ) : ℝ) ≤ stT395o2 50 := by
  have hc : ((93983/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132911980379/1000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((93983/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c51 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-13673/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log ((51 : ℕ)) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((51 : ℕ)) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5059133/10000000) (δ := 2473/250000000) (ψ := -555759/1000000) 395 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t51 : ((-306371680833/5000000000000 : ℚ) : ℝ) ≤ stT395o2 51 := by
  have hc : ((-218793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-306371680833/5000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-218793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c52 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-23831/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log ((52 : ℕ)) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((52 : ℕ)) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2264277/5000000) (δ := 4971/500000000) (ψ := -555759/1000000) 395 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t52 : ((-8263649209/250000000000 : ℚ) : ℝ) ≤ stT395o2 52 := by
  have hc : ((-5959/25000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8263649209/250000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-5959/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c53 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((11852/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log ((53 : ℕ)) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((53 : ℕ)) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1774361/10000000) (δ := 2501/250000000) (ψ := -555759/1000000) 395 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t53 : ((104184917319/1000000000000 : ℚ) : ℝ) ≤ stT395o2 53 := by
  have hc : ((379239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104184917319/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((379239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c54 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-987283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log ((54 : ℕ)) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((54 : ℕ)) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 465929/625000) (δ := 9999/1000000000) (ψ := -555759/1000000) 395 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t54 : ((-335897597931/2500000000000 : ℚ) : ℝ) ≤ stT395o2 54 := by
  have hc : ((-987333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-335897597931/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-987333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c55 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((47419/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log ((55 : ℕ)) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((55 : ℕ)) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 806769/10000000) (δ := 1257/125000000) (ψ := -555759/1000000) 395 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t55 : ((127872722367/1000000000000 : ℚ) : ℝ) ≤ stT395o2 55 := by
  have hc : ((94833/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127872722367/1000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((94833/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c56 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-5909/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log ((56 : ℕ)) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((56 : ℕ)) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -75057/125000) (δ := 10013/1000000000) (ψ := -555759/1000000) 395 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t56 : ((-39483862929/400000000000 : ℚ) : ℝ) ≤ stT395o2 56 := by
  have hc : ((-29547/40000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39483862929/400000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-29547/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c57 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((459071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log ((57 : ℕ)) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((57 : ℕ)) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2734617/10000000) (δ := 497/50000000) (ψ := -555759/1000000) 395 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t57 : ((151997000793/2500000000000 : ℚ) : ℝ) ≤ stT395o2 57 := by
  have hc : ((459021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151997000793/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((459021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c58 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-182631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log ((58 : ℕ)) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((58 : ℕ)) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -877229/2000000) (δ := 9933/1000000000) (ψ := -555759/1000000) 395 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t58 : ((-47974405453/2000000000000 : ℚ) : ℝ) ≤ stT395o2 58 := by
  have hc : ((-182681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47974405453/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-182681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c59 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-12717/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log ((59 : ℕ)) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((59 : ℕ)) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 810843/2000000) (δ := 9933/1000000000) (ψ := -555759/1000000) 395 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t59 : ((-3314481751/500000000000 : ℚ) : ℝ) ≤ stT395o2 59 := by
  have hc : ((-25459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3314481751/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-25459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c60 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((226711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log ((60 : ℕ)) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((60 : ℕ)) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3355243/10000000) (δ := 403/40000000) (ψ := -555759/1000000) 395 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t60 : ((146308995517/5000000000000 : ℚ) : ℝ) ≤ stT395o2 60 := by
  have hc : ((226661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146308995517/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((226661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c61 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-344441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log ((61 : ℕ)) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((61 : ℕ)) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4806099/10000000) (δ := 401/40000000) (ψ := -555759/1000000) 395 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t61 : ((-441075597179/10000000000000 : ℚ) : ℝ) ≤ stT395o2 61 := by
  have hc : ((-344491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-441075597179/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-344491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c62 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((409129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log ((62 : ℕ)) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((62 : ℕ)) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1436621/5000000) (δ := 1977/200000000) (ψ := -555759/1000000) 395 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t62 : ((519530739079/10000000000000 : ℚ) : ℝ) ≤ stT395o2 62 := by
  have hc : ((409079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519530739079/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((409079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c63 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-425927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log ((63 : ℕ)) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((63 : ℕ)) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1005391/2000000) (δ := 2517/250000000) (ψ := -555759/1000000) 395 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t63 : ((-268340377357/5000000000000 : ℚ) : ℝ) ≤ stT395o2 63 := by
  have hc : ((-425977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268340377357/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-425977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c64 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((397401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log ((64 : ℕ)) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((64 : ℕ)) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -581057/2000000) (δ := 10011/1000000000) (ψ := -555759/1000000) 395 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t64 : ((397351/8000000 : ℚ) : ℝ) ≤ stT395o2 64 := by
  have hc : ((397351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((397351/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((397351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c65 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-323257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log ((65 : ℕ)) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((65 : ℕ)) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2374957/5000000) (δ := 9911/1000000000) (ψ := -555759/1000000) 395 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t65 : ((-100253297709/2500000000000 : ℚ) : ℝ) ≤ stT395o2 65 := by
  have hc : ((-323307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100253297709/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-323307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c66 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((100759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log ((66 : ℕ)) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((66 : ℕ)) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3419721/10000000) (δ := 9899/1000000000) (ψ := -555759/1000000) 395 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t66 : ((30998722719/1250000000000 : ℚ) : ℝ) ≤ stT395o2 66 := by
  have hc : ((50367/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30998722719/1250000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((50367/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c67 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-6259/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log ((67 : ℕ)) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((67 : ℕ)) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2002621/5000000) (δ := 619/62500000) (ψ := -555759/1000000) 395 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t67 : ((-1531761191/400000000000 : ℚ) : ℝ) ≤ stT395o2 67 := by
  have hc : ((-6269/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1531761191/400000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-6269/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c68 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-45817/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log ((68 : ℕ)) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((68 : ℕ)) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2193883/5000000) (δ := 10047/1000000000) (ψ := -555759/1000000) 395 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t68 : ((-111152944461/5000000000000 : ℚ) : ℝ) ≤ stT395o2 68 := by
  have hc : ((-91659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111152944461/5000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-91659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c69 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((214163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log ((69 : ℕ)) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((69 : ℕ)) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 352549/1250000) (δ := 4953/500000000) (ψ := -555759/1000000) 395 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t69 : ((64447936101/1250000000000 : ℚ) : ℝ) ≤ stT395o2 69 := by
  have hc : ((107069/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64447936101/1250000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((107069/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c70 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-338053/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log ((70 : ℕ)) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((70 : ℕ)) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5783151/10000000) (δ := 9989/1000000000) (ψ := -555759/1000000) 395 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t70 : ((-202040314931/2500000000000 : ℚ) : ℝ) ≤ stT395o2 70 := by
  have hc : ((-169039/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202040314931/2500000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-169039/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c71 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((883179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log ((71 : ℕ)) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((71 : ℕ)) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 76281/625000) (δ := 629/62500000) (ψ := -555759/1000000) 395 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t71 : ((1048080717749/10000000000000 : ℚ) : ℝ) ≤ stT395o2 71 := by
  have hc : ((883129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1048080717749/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((883129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c72 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-248519/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log ((72 : ℕ)) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((72 : ℕ)) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1895433/2500000) (δ := 9921/1000000000) (ψ := -555759/1000000) 395 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t72 : ((-36612169391/312500000000 : ℚ) : ℝ) ≤ stT395o2 72 := by
  have hc : ((-497063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36612169391/312500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-497063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c73 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((190557/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log ((73 : ℕ)) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((73 : ℕ)) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -77129/1000000) (δ := 9971/1000000000) (ψ := -555759/1000000) 395 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t73 : ((223018304817/2000000000000 : ℚ) : ℝ) ≤ stT395o2 73 := by
  have hc : ((190547/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((223018304817/2000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((190547/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c74 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-180691/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log ((74 : ℕ)) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((74 : ℕ)) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 237859/400000) (δ := 9971/1000000000) (ψ := -555759/1000000) 395 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t74 : ((-420127325139/5000000000000 : ℚ) : ℝ) ≤ stT395o2 74 := by
  have hc : ((-361407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-420127325139/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-361407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c75 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((311967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log ((75 : ℕ)) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((75 : ℕ)) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3133833/10000000) (δ := 397/40000000) (ψ := -555759/1000000) 395 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t75 : ((3601705599/100000000000 : ℚ) : ℝ) ≤ stT395o2 75 := by
  have hc : ((311917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3601705599/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((311917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c76 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((206897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log ((76 : ℕ)) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((76 : ℕ)) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 681197/2000000) (δ := 2507/250000000) (ψ := -555759/1000000) 395 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t76 : ((118634821533/5000000000000 : ℚ) : ℝ) ≤ stT395o2 76 := by
  have hc : ((206847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118634821533/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((206847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c77 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-347441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log ((77 : ℕ)) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((77 : ℕ)) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5847629/10000000) (δ := 1997/200000000) (ψ := -555759/1000000) 395 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t77 : ((-98993584599/1250000000000 : ℚ) : ℝ) ≤ stT395o2 77 := by
  have hc : ((-173733/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98993584599/1250000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-173733/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c78 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((489081/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log ((78 : ℕ)) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((78 : ℕ)) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 16357/312500) (δ := 2517/250000000) (ψ := -555759/1000000) 395 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t78 : ((17304589391/156250000000 : ℚ) : ℝ) ≤ stT395o2 78 := by
  have hc : ((15283/15625 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17304589391/156250000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((15283/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c79 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-914603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log ((79 : ℕ)) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((79 : ℕ)) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3406653/5000000) (δ := 1997/200000000) (ψ := -555759/1000000) 395 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t79 : ((-32158284827/312500000000 : ℚ) : ℝ) ≤ stT395o2 79 := by
  have hc : ((-914653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32158284827/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-914653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c80 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((477007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log ((80 : ℕ)) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((80 : ℕ)) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -21471/80000) (δ := 2473/250000000) (ψ := -555759/1000000) 395 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t80 : ((533253665581/10000000000000 : ℚ) : ℝ) ≤ stT395o2 80 := by
  have hc : ((476957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((533253665581/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((476957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c81 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((37949/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log ((81 : ℕ)) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((81 : ℕ)) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1724867/5000000) (δ := 10011/1000000000) (ψ := -555759/1000000) 395 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t81 : ((42154440229/2000000000000 : ℚ) : ℝ) ≤ stT395o2 81 := by
  have hc : ((37939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42154440229/2000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((37939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c82 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-394491/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log ((82 : ℕ)) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((82 : ℕ)) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6199867/10000000) (δ := 9899/1000000000) (ψ := -555759/1000000) 395 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t82 : ((-27229395691/312500000000 : ℚ) : ℝ) ≤ stT395o2 82 := by
  have hc : ((-98629/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27229395691/312500000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-98629/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c83 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((996307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log ((83 : ℕ)) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((83 : ℕ)) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -107463/5000000) (δ := 4977/500000000) (ψ := -555759/1000000) 395 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t83 : ((546766762997/5000000000000 : ℚ) : ℝ) ≤ stT395o2 83 := by
  have hc : ((996257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((546766762997/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((996257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c84 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-650713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log ((84 : ℕ)) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((84 : ℕ)) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2849149/5000000) (δ := 9927/500000000) (ψ := -555759/1000000) 395 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t84 : ((-71004100167/1000000000000 : ℚ) : ℝ) ≤ stT395o2 84 := by
  have hc : ((-650763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71004100167/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-650763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c85 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-95619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log ((85 : ℕ)) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((85 : ℕ)) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -833281/2000000) (δ := 10007/1000000000) (ψ := -555759/1000000) 395 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t85 : ((-103767667857/10000000000000 : ℚ) : ℝ) ≤ stT395o2 85 := by
  have hc : ((-95669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103767667857/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-95669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c86 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((400031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log ((86 : ℕ)) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((86 : ℕ)) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 321699/2000000) (δ := 10007/1000000000) (ψ := -555759/1000000) 395 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t86 : ((215668634981/2500000000000 : ℚ) : ℝ) ≤ stT395o2 86 := by
  have hc : ((200003/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215668634981/2500000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((200003/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c87 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-488497/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log ((87 : ℕ)) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((87 : ℕ)) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7316689/10000000) (δ := 1237/125000000) (ψ := -555759/1000000) 395 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t87 : ((-261875393493/2500000000000 : ℚ) : ℝ) ≤ stT395o2 87 := by
  have hc : ((-244261/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261875393493/2500000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-244261/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c88 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((454183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log ((88 : ℕ)) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((88 : ℕ)) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1374177/5000000) (δ := 10039/1000000000) (ψ := -555759/1000000) 395 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t88 : ((484107140399/10000000000000 : ℚ) : ℝ) ≤ stT395o2 88 := by
  have hc : ((454133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((484107140399/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((454133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c89 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((424569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log ((89 : ℕ)) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((89 : ℕ)) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 113231/400000) (δ := 629/62500000) (ψ := -555759/1000000) 395 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t89 : ((449988866443/10000000000000 : ℚ) : ℝ) ≤ stT395o2 89 := by
  have hc : ((424519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449988866443/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((424519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c90 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-980571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log ((90 : ℕ)) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((90 : ℕ)) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1840093/2500000) (δ := 2483/250000000) (ψ := -555759/1000000) 395 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t90 : ((-1033665731753/10000000000000 : ℚ) : ℝ) ≤ stT395o2 90 := by
  have hc : ((-980621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1033665731753/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-980621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c91 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((723593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log ((91 : ℕ)) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((91 : ℕ)) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -476127/2500000) (δ := 19921/1000000000) (ψ := -555759/1000000) 395 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t91 : ((189619637553/2500000000000 : ℚ) : ℝ) ≤ stT395o2 91 := by
  have hc : ((723543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189619637553/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((723543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c92 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((86617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log ((92 : ℕ)) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((92 : ℕ)) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 349171/1000000) (δ := 4941/500000000) (ψ := -555759/1000000) 395 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t92 : ((352649979/19531250000 : ℚ) : ℝ) ≤ stT395o2 92 := by
  have hc : ((2706/15625 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352649979/19531250000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((2706/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c93 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-57801/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log ((93 : ℕ)) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((93 : ℕ)) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6878371/10000000) (δ := 2507/250000000) (ψ := -555759/1000000) 395 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t93 : ((-59940103027/625000000000 : ℚ) : ℝ) ≤ stT395o2 93 := by
  have hc : ((-462433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59940103027/625000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-462433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c94 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((802677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log ((94 : ℕ)) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((94 : ℕ)) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1597567/10000000) (δ := 4939/500000000) (ψ := -555759/1000000) 395 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t94 : ((827846342967/10000000000000 : ℚ) : ℝ) ≤ stT395o2 94 := by
  have hc : ((802627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((827846342967/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((802627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c95 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((29893/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log ((95 : ℕ)) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((95 : ℕ)) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 725469/2000000) (δ := 1241/125000000) (ψ := -555759/1000000) 395 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t95 : ((30656735629/2500000000000 : ℚ) : ℝ) ≤ stT395o2 95 := by
  have hc : ((59761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30656735629/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((59761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c96 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-58101/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log ((96 : ℕ)) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((96 : ℕ)) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3455207/5000000) (δ := 1977/200000000) (ψ := -555759/1000000) 395 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t96 : ((-474418321293/5000000000000 : ℚ) : ℝ) ≤ stT395o2 96 := by
  have hc : ((-464833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-474418321293/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-464833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c97 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((753443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log ((97 : ℕ)) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((97 : ℕ)) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -896891/5000000) (δ := 2517/250000000) (ψ := -555759/1000000) 395 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t97 : ((382477284489/5000000000000 : ℚ) : ℝ) ≤ stT395o2 97 := by
  have hc : ((753393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((382477284489/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((753393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c98 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((259641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log ((98 : ℕ)) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((98 : ℕ)) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 654073/2000000) (δ := 5009/500000000) (ψ := -555759/1000000) 395 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t98 : ((32778295979/1250000000000 : ℚ) : ℝ) ≤ stT395o2 98 := by
  have hc : ((259591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32778295979/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((259591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c99 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-123163/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log ((99 : ℕ)) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((99 : ℕ)) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -148497/200000) (δ := 10043/1000000000) (ψ := -555759/1000000) 395 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t99 : ((-247579553363/2500000000000 : ℚ) : ℝ) ≤ stT395o2 99 := by
  have hc : ((-492677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-247579553363/2500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-492677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c100 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((276429/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log ((100 : ℕ)) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((100 : ℕ)) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -492503/2000000) (δ := 249/25000000) (ψ := -555759/1000000) 395 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t100 : ((69100930899/1250000000000 : ℚ) : ℝ) ≤ stT395o2 100 := by
  have hc : ((69101/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69100930899/1250000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((69101/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c101 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((278429/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log ((101 : ℕ)) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((101 : ℕ)) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 490099/2000000) (δ := 249/25000000) (ψ := -555759/1000000) 395 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t101 : ((69255570237/1250000000000 : ℚ) : ℝ) ≤ stT395o2 101 := by
  have hc : ((69601/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69255570237/1250000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((69601/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c102 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-122107/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log ((102 : ℕ)) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((102 : ℕ)) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1828767/2500000) (δ := 1001/100000000) (ψ := -555759/1000000) 395 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t102 : ((-120910190261/1250000000000 : ℚ) : ℝ) ≤ stT395o2 102 := by
  have hc : ((-488453/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120910190261/1250000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-488453/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c103 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((70003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log ((103 : ℕ)) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((103 : ℕ)) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3575821/10000000) (δ := 10053/1000000000) (ψ := -555759/1000000) 395 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t103 : ((34475676381/2500000000000 : ℚ) : ℝ) ≤ stT395o2 103 := by
  have hc : ((34989/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34475676381/2500000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((34989/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c104 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((221991/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log ((104 : ℕ)) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((104 : ℕ)) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1194743/10000000) (δ := 201/20000000) (ψ := -555759/1000000) 395 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t104 : ((21766767753/250000000000 : ℚ) : ℝ) ≤ stT395o2 104 := by
  have hc : ((443957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21766767753/250000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((443957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c105 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-178829/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log ((105 : ℕ)) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((105 : ℕ)) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5919683/10000000) (δ := 9953/1000000000) (ψ := -555759/1000000) 395 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t105 : ((-349063197383/5000000000000 : ℚ) : ℝ) ≤ stT395o2 105 := by
  have hc : ((-357683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-349063197383/5000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-357683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c106 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-455089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log ((106 : ℕ)) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((106 : ℕ)) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1277043/2500000) (δ := 1237/125000000) (ψ := -555759/1000000) 395 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t106 : ((-221035069377/5000000000000 : ℚ) : ℝ) ≤ stT395o2 106 := by
  have hc : ((-455139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221035069377/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-455139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c107 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((982233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log ((107 : ℕ)) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((107 : ℕ)) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -235979/5000000) (δ := 9957/1000000000) (ψ := -555759/1000000) 395 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t107 : ((59344479043/625000000000 : ℚ) : ℝ) ≤ stT395o2 107 := by
  have hc : ((982183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59344479043/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((982183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c108 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-38783/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log ((108 : ℕ)) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((108 : ℕ)) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2060551/5000000) (δ := 9957/1000000000) (ψ := -555759/1000000) 395 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t108 : ((-4667879601/625000000000 : ℚ) : ℝ) ≤ stT395o2 108 := by
  have hc : ((-4851/62500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4667879601/625000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-4851/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c109 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-94697/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log ((109 : ℕ)) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((109 : ℕ)) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1407233/2000000) (δ := 2491/250000000) (ψ := -555759/1000000) 395 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t109 : ((-45354066277/500000000000 : ℚ) : ℝ) ≤ stT395o2 109 := by
  have hc : ((-47351/50000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45354066277/500000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-47351/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c110 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((106237/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log ((110 : ℕ)) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((110 : ℕ)) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2526993/10000000) (δ := 5007/500000000) (ψ := -555759/1000000) 395 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t110 : ((50641703937/1000000000000 : ℚ) : ℝ) ≤ stT395o2 110 := by
  have hc : ((106227/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50641703937/1000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((106227/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c111 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((71333/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log ((111 : ℕ)) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((111 : ℕ)) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 388279/2000000) (δ := 2491/250000000) (ψ := -555759/1000000) 395 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t111 : ((2115670953/31250000000 : ℚ) : ℝ) ≤ stT395o2 111 := by
  have hc : ((2229/3125 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2115670953/31250000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((2229/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c112 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-103607/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log ((112 : ℕ)) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((112 : ℕ)) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6369641/10000000) (δ := 9889/1000000000) (ψ := -555759/1000000) 395 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t112 : ((-24476350821/312500000000 : ℚ) : ℝ) ≤ stT395o2 112 := by
  have hc : ((-414453/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24476350821/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-414453/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c113 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-397651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log ((113 : ℕ)) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((113 : ℕ)) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2474689/5000000) (δ := 10071/1000000000) (ψ := -555759/1000000) 395 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t113 : ((-374125682421/10000000000000 : ℚ) : ℝ) ≤ stT395o2 113 := by
  have hc : ((-397701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-374125682421/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-397701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c114 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((971419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log ((114 : ℕ)) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((114 : ℕ)) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -119829/2000000) (δ := 4991/500000000) (ψ := -555759/1000000) 395 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t114 : ((181953926973/2000000000000 : ℚ) : ℝ) ≤ stT395o2 114 := by
  have hc : ((971369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181953926973/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((971369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c115 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((21361/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log ((115 : ℕ)) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((115 : ℕ)) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 23207/62500) (δ := 10021/1000000000) (ψ := -555759/1000000) 395 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t115 : ((4976890411/625000000000 : ℚ) : ℝ) ≤ stT395o2 115 := by
  have hc : ((42697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4976890411/625000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((42697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c116 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-998563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log ((116 : ℕ)) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((116 : ℕ)) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1929989/2500000) (δ := 1241/125000000) (ψ := -555759/1000000) 395 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t116 : ((-927189202401/10000000000000 : ℚ) : ℝ) ≤ stT395o2 116 := by
  have hc : ((-998613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-927189202401/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-998613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c117 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((88587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log ((117 : ℕ)) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((117 : ℕ)) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -696341/2000000) (δ := 397/40000000) (ψ := -555759/1000000) 395 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t117 : ((81875569/5000000000 : ℚ) : ℝ) ≤ stT395o2 117 := by
  have hc : ((44281/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81875569/5000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((44281/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c118 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((479381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log ((118 : ℕ)) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((118 : ℕ)) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 720453/10000000) (δ := 399/40000000) (ψ := -555759/1000000) 395 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t118 : ((55160333793/625000000000 : ℚ) : ℝ) ≤ stT395o2 118 := by
  have hc : ((119839/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55160333793/625000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((119839/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c119 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-374677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log ((119 : ℕ)) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((119 : ℕ)) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4887111/10000000) (δ := 4989/500000000) (ψ := -555759/1000000) 395 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t119 : ((-343511866173/10000000000000 : ℚ) : ℝ) ≤ stT395o2 119 := by
  have hc : ((-374727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-343511866173/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-374727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c120 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-893377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log ((120 : ℕ)) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((120 : ℕ)) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1672251/2500000) (δ := 2509/250000000) (ψ := -555759/1000000) 395 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t120 : ((-815583598917/10000000000000 : ℚ) : ℝ) ≤ stT395o2 120 := by
  have hc : ((-893427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-815583598917/10000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-893427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c121 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((509159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log ((121 : ℕ)) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((121 : ℕ)) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -161967/625000) (δ := 9917/1000000000) (ψ := -555759/1000000) 395 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t121 : ((46282590081/1000000000000 : ℚ) : ℝ) ≤ stT395o2 121 := by
  have hc : ((509109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46282590081/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((509109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c122 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((831533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log ((122 : ℕ)) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((122 : ℕ)) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1472337/10000000) (δ := 10067/1000000000) (ψ := -555759/1000000) 395 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t122 : ((752788954431/10000000000000 : ℚ) : ℝ) ≤ stT395o2 122 := by
  have hc : ((831483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((752788954431/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((831483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c123 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-29473/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log ((123 : ℕ)) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((123 : ℕ)) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5502967/10000000) (δ := 621/62500000) (ψ := -555759/1000000) 395 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t123 : ((-5315434817/100000000000 : ℚ) : ℝ) ≤ stT395o2 123 := by
  have hc : ((-58951/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5315434817/100000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-58951/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c124 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-790733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log ((124 : ℕ)) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((124 : ℕ)) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1551751/2500000) (δ := 991/100000000) (ψ := -555759/1000000) 395 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t124 : ((-710144485141/10000000000000 : ℚ) : ℝ) ≤ stT395o2 124 := by
  have hc : ((-790783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-710144485141/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-790783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c125 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((624393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log ((125 : ℕ)) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((125 : ℕ)) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -448221/2000000) (δ := 9943/1000000000) (ψ := -555759/1000000) 395 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t125 : ((558429236461/10000000000000 : ℚ) : ℝ) ≤ stT395o2 125 := by
  have hc : ((624343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((558429236461/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((624343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c126 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((389641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log ((126 : ℕ)) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((126 : ℕ)) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 846597/5000000) (δ := 10043/1000000000) (ψ := -555759/1000000) 395 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t126 : ((2169357537/31250000000 : ℚ) : ℝ) ≤ stT395o2 126 := by
  have hc : ((24351/31250 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2169357537/31250000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((24351/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c127 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-154803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log ((127 : ℕ)) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((127 : ℕ)) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5596337/10000000) (δ := 9993/1000000000) (ψ := -555759/1000000) 395 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t127 : ((-274753235267/5000000000000 : ℚ) : ℝ) ≤ stT395o2 127 := by
  have hc : ((-309631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274753235267/5000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-309631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c128 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-399257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log ((128 : ℕ)) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((128 : ℕ)) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6239047/10000000) (δ := 10053/1000000000) (ψ := -555759/1000000) 395 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t128 : ((-44114871411/625000000000 : ℚ) : ℝ) ≤ stT395o2 128 := by
  have hc : ((-199641/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44114871411/625000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-199641/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c129 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((287319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log ((129 : ℕ)) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((129 : ℕ)) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -479317/2000000) (δ := 1/100000) (ψ := -555759/1000000) 395 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t129 : ((2529480023/50000000000 : ℚ) : ℝ) ≤ stT395o2 129 := by
  have hc : ((143647/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2529480023/50000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((143647/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c130 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((421903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log ((130 : ℕ)) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((130 : ℕ)) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 177019/1250000) (δ := 9953/1000000000) (ψ := -555759/1000000) 395 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t130 : ((92502868731/1250000000000 : ℚ) : ℝ) ≤ stT395o2 130 := by
  have hc : ((210939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92502868731/1250000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((210939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c131 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-24369/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log ((131 : ℕ)) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((131 : ℕ)) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5199709/10000000) (δ := 9903/1000000000) (ψ := -555759/1000000) 395 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t131 : ((-8517400563/200000000000 : ℚ) : ℝ) ≤ stT395o2 131 := by
  have hc : ((-48743/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8517400563/200000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-48743/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c132 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-904667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log ((132 : ℕ)) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((132 : ℕ)) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6753483/10000000) (δ := 1237/125000000) (ψ := -555759/1000000) 395 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t132 : ((-787455724913/10000000000000 : ℚ) : ℝ) ≤ stT395o2 132 := by
  have hc : ((-904717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-787455724913/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-904717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c133 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((352251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log ((133 : ℕ)) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((133 : ℕ)) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3027053/10000000) (δ := 1237/125000000) (ψ := -555759/1000000) 395 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t133 : ((305396656909/10000000000000 : ℚ) : ℝ) ≤ stT395o2 133 := by
  have hc : ((352201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((305396656909/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((352201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c134 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((241037/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log ((134 : ℕ)) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((134 : ℕ)) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 134291/2000000) (δ := 9973/500000000) (ψ := -555759/1000000) 395 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t134 : ((104106676383/1250000000000 : ℚ) : ℝ) ≤ stT395o2 134 := by
  have hc : ((482049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104106676383/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((482049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c135 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-6617/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log ((135 : ℕ)) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((135 : ℕ)) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2171231/5000000) (δ := 1237/125000000) (ψ := -555759/1000000) 395 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t135 : ((-5696728397/400000000000 : ℚ) : ℝ) ≤ stT395o2 135 := by
  have hc : ((-6619/40000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5696728397/400000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-6619/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c136 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-499299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log ((136 : ℕ)) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((136 : ℕ)) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7721577/10000000) (δ := 9939/1000000000) (ψ := -555759/1000000) 395 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t136 : ((-107041708683/1250000000000 : ℚ) : ℝ) ≤ stT395o2 136 := by
  have hc : ((-124831/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107041708683/1250000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-124831/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c137 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-7087/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log ((137 : ℕ)) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((137 : ℕ)) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -820863/2000000) (δ := 9889/1000000000) (ψ := -555759/1000000) 395 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t137 : ((-757388367/125000000000 : ℚ) : ℝ) ≤ stT395o2 137 := by
  have hc : ((-1773/25000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-757388367/125000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-1773/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c138 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((489493/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log ((138 : ℕ)) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((138 : ℕ)) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -513419/10000000) (δ := 5007/500000000) (ψ := -555759/1000000) 395 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t138 : ((13020705369/156250000000 : ℚ) : ℝ) ≤ stT395o2 138 := by
  have hc : ((122367/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13020705369/156250000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((122367/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c139 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((343043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log ((139 : ℕ)) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((139 : ℕ)) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 762901/2500000) (δ := 2491/250000000) (ψ := -555759/1000000) 395 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t139 : ((72730636671/2500000000000 : ℚ) : ℝ) ≤ stT395o2 139 := by
  have hc : ((342993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72730636671/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((342993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c140 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-875091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log ((140 : ℕ)) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((140 : ℕ)) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6591051/10000000) (δ := 5007/500000000) (ψ := -555759/1000000) 395 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t140 : ((-147925958371/2000000000000 : ℚ) : ℝ) ≤ stT395o2 140 := by
  have hc : ((-875141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147925958371/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-875141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c141 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-621207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log ((141 : ℕ)) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((141 : ℕ)) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -700337/1250000) (δ := 5011/500000000) (ψ := -555759/1000000) 395 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t141 : ((-65399103133/1250000000000 : ℚ) : ℝ) ≤ stT395o2 141 := by
  have hc : ((-621257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65399103133/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-621257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c142 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((331751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log ((142 : ℕ)) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((142 : ℕ)) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1056633/5000000) (δ := 5011/500000000) (ψ := -555759/1000000) 395 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t142 : ((139189078203/2500000000000 : ℚ) : ℝ) ≤ stT395o2 142 := by
  have hc : ((165863/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139189078203/2500000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((165863/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c143 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((214341/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log ((143 : ℕ)) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((143 : ℕ)) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 675837/5000000) (δ := 5011/500000000) (ψ := -555759/1000000) 395 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t143 : ((179230493497/2500000000000 : ℚ) : ℝ) ≤ stT395o2 143 := by
  have hc : ((428657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179230493497/2500000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((428657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c144 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-339299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log ((144 : ℕ)) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((144 : ℕ)) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 239621/500000) (δ := 4961/500000000) (ψ := -555759/1000000) 395 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t144 : ((-141395529783/5000000000000 : ℚ) : ℝ) ≤ stT395o2 144 := by
  have hc : ((-339349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141395529783/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-339349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c145 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-98991/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log ((145 : ℕ)) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((145 : ℕ)) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7498547/10000000) (δ := 5037/500000000) (ψ := -555759/1000000) 395 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t145 : ((-4110586159/50000000000 : ℚ) : ℝ) ≤ stT395o2 145 := by
  have hc : ((-24749/25000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4110586159/50000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-24749/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c146 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-17791/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log ((146 : ℕ)) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((146 : ℕ)) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1026263/2500000) (δ := 9929/1000000000) (ψ := -555759/1000000) 395 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t146 : ((-14734283421/2500000000000 : ℚ) : ℝ) ≤ stT395o2 146 := by
  have hc : ((-35607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14734283421/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-35607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c147 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((2991/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log ((147 : ℕ)) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((147 : ℕ)) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -183691/2500000) (δ := 9879/1000000000) (ψ := -555759/1000000) 395 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t147 : ((39468896851/500000000000 : ℚ) : ℝ) ≤ stT395o2 147 := by
  have hc : ((95707/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39468896851/500000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((95707/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c148 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((125457/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log ((148 : ℕ)) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((148 : ℕ)) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2612713/10000000) (δ := 9929/1000000000) (ψ := -555759/1000000) 395 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t148 : ((103114626333/2500000000000 : ℚ) : ℝ) ≤ stT395o2 148 := by
  have hc : ((250889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103114626333/2500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((250889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c149 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-720327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log ((149 : ℕ)) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((149 : ℕ)) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 237507/400000) (δ := 9979/1000000000) (ψ := -555759/1000000) 395 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t149 : ((-18442371577/312500000000 : ℚ) : ℝ) ≤ stT395o2 149 := by
  have hc : ((-720377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18442371577/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-720377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c150 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-170029/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log ((150 : ℕ)) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((150 : ℕ)) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1616911/2500000) (δ := 621/62500000) (ψ := -555759/1000000) 395 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t150 : ((-138836333383/2000000000000 : ℚ) : ℝ) ≤ stT395o2 150 := by
  have hc : ((-170039/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138836333383/2000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-170039/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c151 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((145871/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log ((151 : ℕ)) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((151 : ℕ)) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3186873/10000000) (δ := 9917/1000000000) (ψ := -555759/1000000) 395 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t151 : ((14835965581/625000000000 : ℚ) : ℝ) ≤ stT395o2 151 := by
  have hc : ((72923/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14835965581/625000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((72923/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c152 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((999583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log ((152 : ℕ)) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((152 : ℕ)) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 72223/10000000) (δ := 4993/500000000) (ψ := -555759/1000000) 395 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t152 : ((810728213031/10000000000000 : ℚ) : ℝ) ≤ stT395o2 152 := by
  have hc : ((999533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((810728213031/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((999533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c153 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((122161/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log ((153 : ℕ)) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((153 : ℕ)) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3309939/10000000) (δ := 4943/500000000) (ψ := -555759/1000000) 395 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t153 : ((3085659171/156250000000 : ℚ) : ℝ) ≤ stT395o2 153 := by
  have hc : ((15267/62500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3085659171/156250000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((15267/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c154 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-862319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log ((154 : ℕ)) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((154 : ℕ)) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1631643/2500000) (δ := 9917/1000000000) (ψ := -555759/1000000) 395 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t154 : ((-694916774687/10000000000000 : ℚ) : ℝ) ≤ stT395o2 154 := by
  have hc : ((-862369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-694916774687/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-862369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c155 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-733489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log ((155 : ℕ)) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((155 : ℕ)) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2992797/5000000) (δ := 9993/1000000000) (ψ := -555759/1000000) 395 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t155 : ((-29459659779/500000000000 : ℚ) : ℝ) ≤ stT395o2 155 := by
  have hc : ((-733539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29459659779/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-733539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c156 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((431957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log ((156 : ℕ)) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((156 : ℕ)) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2810337/10000000) (δ := 10043/1000000000) (ψ := -555759/1000000) 395 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t156 : ((540315657/15625000000 : ℚ) : ℝ) ≤ stT395o2 156 := by
  have hc : ((431907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((540315657/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((431907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c157 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((495257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log ((157 : ℕ)) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((157 : ℕ)) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 172313/5000000) (δ := 1001/100000000) (ψ := -555759/1000000) 395 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t157 : ((1543897367/19531250000 : ℚ) : ℝ) ≤ stT395o2 157 := by
  have hc : ((15476/15625 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1543897367/19531250000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((15476/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c158 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((7121/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log ((158 : ℕ)) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((158 : ℕ)) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 434943/1250000) (δ := 9943/1000000000) (ψ := -555759/1000000) 395 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t158 : ((5663570283/400000000000 : ℚ) : ℝ) ≤ stT395o2 158 := by
  have hc : ((7119/40000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5663570283/400000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((7119/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c159 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-875799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log ((159 : ℕ)) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((159 : ℕ)) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6594711/10000000) (δ := 1001/100000000) (ψ := -555759/1000000) 395 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t159 : ((-173648450287/2500000000000 : ℚ) : ℝ) ≤ stT395o2 159 := by
  have hc : ((-875849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173648450287/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-875849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c160 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-742141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log ((160 : ℕ)) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((160 : ℕ)) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6017637/10000000) (δ := 9903/1000000000) (ψ := -555759/1000000) 395 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t160 : ((-58675393887/1000000000000 : ℚ) : ℝ) ≤ stT395o2 160 := by
  have hc : ((-742191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58675393887/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-742191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c161 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((38413/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log ((161 : ℕ)) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((161 : ℕ)) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -183833/625000) (δ := 10053/1000000000) (ψ := -555759/1000000) 395 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t161 : ((378371611/12500000000 : ℚ) : ℝ) ≤ stT395o2 161 := by
  have hc : ((4801/12500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((378371611/12500000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((4801/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c162 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((249731/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log ((162 : ℕ)) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((162 : ℕ)) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 28993/2500000) (δ := 10053/1000000000) (ψ := -555759/1000000) 395 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t162 : ((196197332769/2500000000000 : ℚ) : ℝ) ≤ stT395o2 162 := by
  have hc : ((499437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196197332769/2500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((499437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c163 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((152059/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log ((163 : ℕ)) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((163 : ℕ)) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3154461/10000000) (δ := 201/20000000) (ψ := -555759/1000000) 395 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t163 : ((2977053771/125000000000 : ℚ) : ℝ) ≤ stT395o2 163 := by
  have hc : ((76017/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2977053771/125000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((76017/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c164 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-391333/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log ((164 : ℕ)) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((164 : ℕ)) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3087167/5000000) (δ := 10003/1000000000) (ψ := -555759/1000000) 395 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t164 : ((-152799665051/2500000000000 : ℚ) : ℝ) ≤ stT395o2 164 := by
  have hc : ((-195679/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152799665051/2500000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-195679/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c165 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-431721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log ((165 : ℕ)) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((165 : ℕ)) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6532123/10000000) (δ := 2499/250000000) (ψ := -555759/1000000) 395 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t165 : ((-168056914627/2500000000000 : ℚ) : ℝ) ≤ stT395o2 165 := by
  have hc : ((-215873/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168056914627/2500000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-215873/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c166 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((6029/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log ((166 : ℕ)) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((166 : ℕ)) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3548737/10000000) (δ := 9907/1000000000) (ψ := -555759/1000000) 395 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t166 : ((93557121/8000000000 : ℚ) : ℝ) ≤ stT395o2 166 := by
  have hc : ((6027/40000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93557121/8000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((6027/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c167 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((972911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log ((167 : ℕ)) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((167 : ℕ)) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -23329/400000) (δ := 9957/1000000000) (ψ := -555759/1000000) 395 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t167 : ((752822217603/10000000000000 : ℚ) : ℝ) ≤ stT395o2 167 := by
  have hc : ((972861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((752822217603/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((972861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c168 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((58509/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log ((168 : ℕ)) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((168 : ℕ)) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 73891/312500) (δ := 10007/1000000000) (ψ := -555759/1000000) 395 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t168 : ((1410524127/31250000000 : ℚ) : ℝ) ≤ stT395o2 168 := by
  have hc : ((7313/12500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1410524127/31250000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((7313/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c169 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-520239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log ((169 : ℕ)) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((169 : ℕ)) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5294819/10000000) (δ := 4973/500000000) (ψ := -555759/1000000) 395 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t169 : ((-400222427759/10000000000000 : ℚ) : ℝ) ≤ stT395o2 169 := by
  have hc : ((-520289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400222427759/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-520289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c170 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-495001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log ((170 : ℕ)) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((170 : ℕ)) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7500167/10000000) (δ := 1993/200000000) (ψ := -555759/1000000) 395 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t170 : ((-37966761609/500000000000 : ℚ) : ℝ) ≤ stT395o2 170 := by
  have hc : ((-247513/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37966761609/500000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-247513/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c171 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-66903/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log ((171 : ℕ)) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((171 : ℕ)) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2302137/5000000) (δ := 1983/200000000) (ψ := -555759/1000000) 395 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t171 : ((-1279290529/62500000000 : ℚ) : ℝ) ≤ stT395o2 171 := by
  have hc : ((-133831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1279290529/62500000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-133831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c172 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((385589/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log ((172 : ℕ)) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((172 : ℕ)) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1725267/10000000) (δ := 1993/200000000) (ψ := -555759/1000000) 395 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t172 : ((18374341593/312500000000 : ℚ) : ℝ) ≤ stT395o2 172 := by
  have hc : ((96391/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18374341593/312500000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((96391/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c173 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((44917/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log ((173 : ℕ)) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((173 : ℕ)) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1137051/10000000) (δ := 1983/200000000) (ψ := -555759/1000000) 395 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t173 : ((13659128253/200000000000 : ℚ) : ℝ) ≤ stT395o2 173 := by
  have hc : ((89829/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13659128253/200000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((89829/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c174 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-22353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log ((174 : ℕ)) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((174 : ℕ)) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1991439/5000000) (δ := 1993/200000000) (ψ := -555759/1000000) 395 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t174 : ((-16983691897/10000000000000 : ℚ) : ℝ) ≤ stT395o2 174 := by
  have hc : ((-22403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16983691897/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-22403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c175 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-914459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log ((175 : ℕ)) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((175 : ℕ)) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6812411/10000000) (δ := 1983/200000000) (ψ := -555759/1000000) 395 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t175 : ((-691303873861/10000000000000 : ℚ) : ℝ) ≤ stT395o2 175 := by
  have hc : ((-914509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-691303873861/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-914509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c176 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-759191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log ((176 : ℕ)) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((176 : ℕ)) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1216433/2000000) (δ := 9931/1000000000) (ψ := -555759/1000000) 395 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t176 : ((-572299921739/10000000000000 : ℚ) : ℝ) ≤ stT395o2 176 := by
  have hc : ((-759241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-572299921739/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-759241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c177 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((254109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log ((177 : ℕ)) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((177 : ℕ)) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -821169/2500000) (δ := 4961/500000000) (ψ := -555759/1000000) 395 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t177 : ((95481215557/5000000000000 : ℚ) : ℝ) ≤ stT395o2 177 := by
  have hc : ((254059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95481215557/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((254059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c178 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((979829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log ((178 : ℕ)) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((178 : ℕ)) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -502987/10000000) (δ := 5011/500000000) (ψ := -555759/1000000) 395 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t178 : ((734374733649/10000000000000 : ℚ) : ℝ) ≤ stT395o2 178 := by
  have hc : ((979779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((734374733649/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((979779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c179 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((308741/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log ((179 : ℕ)) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((179 : ℕ)) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 565787/2500000) (δ := 9981/1000000000) (ψ := -555759/1000000) 395 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t179 : ((11537257173/250000000000 : ℚ) : ℝ) ≤ stT395o2 179 := by
  have hc : ((77179/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11537257173/250000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((77179/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c180 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-421171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log ((180 : ℕ)) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((180 : ℕ)) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 501383/1000000) (δ := 1259/125000000) (ψ := -555759/1000000) 395 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t180 : ((-78489899919/2500000000000 : ℚ) : ℝ) ≤ stT395o2 180 := by
  have hc : ((-421221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78489899919/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-421221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c181 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-249781/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log ((181 : ℕ)) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((181 : ℕ)) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7749303/10000000) (δ := 9981/1000000000) (ψ := -555759/1000000) 395 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t181 : ((-74268103833/1000000000000 : ℚ) : ℝ) ≤ stT395o2 181 := by
  have hc : ((-499587/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74268103833/1000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-499587/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c182 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-500799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log ((182 : ℕ)) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((182 : ℕ)) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1047659/2000000) (δ := 9879/1000000000) (ψ := -555759/1000000) 395 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t182 : ((-297003457/8000000000 : ℚ) : ℝ) ≤ stT395o2 182 := by
  have hc : ((-500849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297003457/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-500849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c183 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((529219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log ((183 : ℕ)) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((183 : ℕ)) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -316599/1250000) (δ := 2481/250000000) (ψ := -555759/1000000) 395 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t183 : ((391172837349/10000000000000 : ℚ) : ℝ) ≤ stT395o2 183 := by
  have hc : ((529169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391172837349/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((529169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c184 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((199601/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log ((184 : ℕ)) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((184 : ℕ)) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 39487/2500000) (δ := 2481/250000000) (ψ := -555759/1000000) 395 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t184 : ((147140281519/2000000000000 : ℚ) : ℝ) ≤ stT395o2 184 := by
  have hc : ((199591/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147140281519/2000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((199591/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c185 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((423357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log ((185 : ℕ)) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((185 : ℕ)) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1417061/5000000) (δ := 5037/500000000) (ψ := -555759/1000000) 395 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t185 : ((155610616349/5000000000000 : ℚ) : ℝ) ≤ stT395o2 185 := by
  have hc : ((423307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155610616349/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((423307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c186 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-36697/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log ((186 : ℕ)) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((186 : ℕ)) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 549583/1000000) (δ := 9879/1000000000) (ψ := -555759/1000000) 395 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t186 : ((-53819705709/1250000000000 : ℚ) : ℝ) ≤ stT395o2 186 := by
  have hc : ((-293601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53819705709/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-293601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c187 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-99331/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log ((187 : ℕ)) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((187 : ℕ)) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3782323/5000000) (δ := 9967/1000000000) (ψ := -555759/1000000) 395 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t187 : ((-9080216841/125000000000 : ℚ) : ℝ) ≤ stT395o2 187 := by
  have hc : ((-12417/12500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9080216841/125000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-12417/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c188 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-48877/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log ((188 : ℕ)) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((188 : ℕ)) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4931329/10000000) (δ := 9917/1000000000) (ψ := -555759/1000000) 395 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t188 : ((-5704284209/200000000000 : ℚ) : ℝ) ≤ stT395o2 188 := by
  have hc : ((-195533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5704284209/200000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-195533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c189 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((120403/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log ((189 : ℕ)) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((189 : ℕ)) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -18062/78125) (δ := 9967/1000000000) (ψ := -555759/1000000) 395 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t189 : ((2736653283/62500000000 : ℚ) : ℝ) ≤ stT395o2 189 := by
  have hc : ((120393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2736653283/62500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((120393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c190 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((993113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log ((190 : ℕ)) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((190 : ℕ)) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 293583/10000000) (δ := 4943/500000000) (ψ := -555759/1000000) 395 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t190 : ((180110843247/2500000000000 : ℚ) : ℝ) ≤ stT395o2 190 := by
  have hc : ((993063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180110843247/2500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((993063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c191 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((20233/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log ((191 : ℕ)) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((191 : ℕ)) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1442737/5000000) (δ := 9967/1000000000) (ψ := -555759/1000000) 395 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t191 : ((14638263807/500000000000 : ℚ) : ℝ) ≤ stT395o2 191 := by
  have hc : ((40461/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14638263807/500000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((40461/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c192 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-576729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log ((192 : ℕ)) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((192 : ℕ)) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5463787/10000000) (δ := 10017/1000000000) (ψ := -555759/1000000) 395 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t192 : ((-52031810369/1250000000000 : ℚ) : ℝ) ≤ stT395o2 192 := by
  have hc : ((-576779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52031810369/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-576779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c193 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-498779/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log ((193 : ℕ)) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((193 : ℕ)) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7679243/10000000) (δ := 10043/1000000000) (ψ := -555759/1000000) 395 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t193 : ((-11220221877/156250000000 : ℚ) : ℝ) ≤ stT395o2 193 := by
  have hc : ((-124701/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11220221877/156250000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-124701/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c194 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-18479/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log ((194 : ℕ)) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((194 : ℕ)) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5127543/10000000) (δ := 10043/1000000000) (ψ := -555759/1000000) 395 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t194 : ((-13268600279/400000000000 : ℚ) : ℝ) ≤ stT395o2 194 := by
  have hc : ((-18481/40000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13268600279/400000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-18481/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c195 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((255009/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log ((195 : ℕ)) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((195 : ℕ)) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2588977/10000000) (δ := 9943/1000000000) (ψ := -555759/1000000) 395 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t195 : ((11412350761/312500000000 : ℚ) : ℝ) ≤ stT395o2 195 := by
  have hc : ((31873/62500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11412350761/312500000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((31873/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c196 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((499839/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log ((196 : ℕ)) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((196 : ℕ)) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -63397/10000000) (δ := 503/50000000) (ψ := -555759/1000000) 395 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t196 : ((35700964299/500000000000 : ℚ) : ℝ) ≤ stT395o2 196 := by
  have hc : ((249907/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35700964299/500000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((249907/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c197 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((557239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log ((197 : ℕ)) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((197 : ℕ)) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2449347/10000000) (δ := 10043/1000000000) (ψ := -555759/1000000) 395 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t197 : ((39698044683/1000000000000 : ℚ) : ℝ) ≤ stT395o2 197 := by
  have hc : ((557189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39698044683/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((557189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c198 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-397641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log ((198 : ℕ)) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((198 : ℕ)) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4949351/10000000) (δ := 9893/1000000000) (ψ := -555759/1000000) 395 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t198 : ((-28262706297/1000000000000 : ℚ) : ℝ) ≤ stT395o2 198 := by
  have hc : ((-397691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28262706297/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-397691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c199 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-986107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log ((199 : ℕ)) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((199 : ℕ)) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1487353/2000000) (δ := 9993/1000000000) (ψ := -555759/1000000) 395 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t199 : ((-349534473237/5000000000000 : ℚ) : ℝ) ≤ stT395o2 199 := by
  have hc : ((-986157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-349534473237/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-986157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c200 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-135993/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log ((200 : ℕ)) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((200 : ℕ)) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5796277/10000000) (δ := 10003/1000000000) (ψ := -555759/1000000) 395 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t200 : ((-96168673321/2000000000000 : ℚ) : ℝ) ≤ stT395o2 200 := by
  have hc : ((-136003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96168673321/2000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-136003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c201 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((47023/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log ((201 : ℕ)) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((201 : ℕ)) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3333649/10000000) (δ := 199/20000000) (ψ := -555759/1000000) 395 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t201 : ((6632076897/400000000000 : ℚ) : ℝ) ≤ stT395o2 201 := by
  have hc : ((47013/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6632076897/400000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((47013/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c202 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((938227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log ((202 : ℕ)) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((202 : ℕ)) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -220829/2500000) (δ := 99/10000000) (ψ := -555759/1000000) 395 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t202 : ((660098522669/10000000000000 : ℚ) : ℝ) ≤ stT395o2 202 := by
  have hc : ((938177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((660098522669/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((938177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c203 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((406361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log ((203 : ℕ)) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((203 : ℕ)) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 155497/1000000) (δ := 201/20000000) (ψ := -555759/1000000) 395 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t203 : ((2228060919/39062500000 : ℚ) : ℝ) ≤ stT395o2 203 := by
  have hc : ((12698/15625 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2228060919/39062500000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((12698/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c204 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-4341/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log ((204 : ℕ)) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((204 : ℕ)) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3981257/10000000) (δ := 9903/1000000000) (ψ := -555759/1000000) 395 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t204 : ((-3046313491/2000000000000 : ℚ) : ℝ) ≤ stT395o2 204 := by
  have hc : ((-4351/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3046313491/2000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-4351/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c205 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-417321/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log ((205 : ℕ)) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((205 : ℕ)) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1279139/2000000) (δ := 201/20000000) (ψ := -555759/1000000) 395 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t205 : ((-145743692063/2500000000000 : ℚ) : ℝ) ≤ stT395o2 205 := by
  have hc : ((-208673/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145743692063/2500000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-208673/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c206 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-929493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log ((206 : ℕ)) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((206 : ℕ)) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3454791/5000000) (δ := 5029/500000000) (ψ := -555759/1000000) 395 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t206 : ((-323822106281/5000000000000 : ℚ) : ℝ) ≤ stT395o2 206 := by
  have hc : ((-929543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-323822106281/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-929543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c207 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-234421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log ((207 : ℕ)) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((207 : ℕ)) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4518549/10000000) (δ := 1999/200000000) (ψ := -555759/1000000) 395 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t207 : ((-162968834079/10000000000000 : ℚ) : ℝ) ≤ stT395o2 207 := by
  have hc : ((-234471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162968834079/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-234471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c208 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((8197/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log ((208 : ℕ)) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((208 : ℕ)) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2139019/10000000) (δ := 1251/125000000) (ψ := -555759/1000000) 395 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t208 : ((363722337/8000000000 : ℚ) : ℝ) ≤ stT395o2 208 := by
  have hc : ((65571/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((363722337/8000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((65571/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c209 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((248951/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log ((209 : ℕ)) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((209 : ℕ)) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 14319/625000) (δ := 2009/200000000) (ψ := -555759/1000000) 395 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t209 : ((172194245589/2500000000000 : ℚ) : ℝ) ≤ stT395o2 209 := by
  have hc : ((497877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172194245589/2500000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((497877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c210 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((511069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log ((210 : ℕ)) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((210 : ℕ)) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2585921/10000000) (δ := 1999/200000000) (ψ := -555759/1000000) 395 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t210 : ((70527265247/2000000000000 : ℚ) : ℝ) ≤ stT395o2 210 := by
  have hc : ((511019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70527265247/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((511019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c211 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-39109/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log ((211 : ℕ)) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((211 : ℕ)) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 493153/1000000) (δ := 1979/200000000) (ψ := -555759/1000000) 395 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t211 : ((-13463605953/500000000000 : ℚ) : ℝ) ≤ stT395o2 211 := by
  have hc : ((-19557/50000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13463605953/500000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-19557/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c212 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-121559/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log ((212 : ℕ)) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((212 : ℕ)) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7266029/10000000) (δ := 2009/200000000) (ψ := -555759/1000000) 395 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t212 : ((-333965513583/5000000000000 : ℚ) : ℝ) ≤ stT395o2 212 := by
  have hc : ((-486261/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333965513583/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-486261/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c213 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-24017/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log ((213 : ℕ)) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((213 : ℕ)) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1529599/2500000) (δ := 2497/250000000) (ψ := -555759/1000000) 395 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t213 : ((-263316077133/5000000000000 : ℚ) : ℝ) ≤ stT395o2 213 := by
  have hc : ((-384297/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-263316077133/5000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-384297/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c214 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((48489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log ((214 : ℕ)) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((214 : ℕ)) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -95143/250000) (δ := 1983/200000000) (ψ := -555759/1000000) 395 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t214 : ((6622434763/2000000000000 : ℚ) : ℝ) ≤ stT395o2 214 := by
  have hc : ((48439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6622434763/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((48439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c215 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((824463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log ((215 : ℕ)) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((215 : ℕ)) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -751929/5000000) (δ := 5019/500000000) (ψ := -555759/1000000) 395 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t215 : ((281122359761/5000000000000 : ℚ) : ℝ) ≤ stT395o2 215 := by
  have hc : ((824413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((281122359761/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((824413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c216 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((29713/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log ((216 : ℕ)) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((216 : ℕ)) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 39367/500000) (δ := 1983/200000000) (ψ := -555759/1000000) 395 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t216 : ((323456773179/5000000000000 : ℚ) : ℝ) ≤ stT395o2 216 := by
  have hc : ((475383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((323456773179/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((475383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c217 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((67381/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log ((217 : ℕ)) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((217 : ℕ)) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1533961/5000000) (δ := 1993/200000000) (ψ := -555759/1000000) 395 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t217 : ((11433599781/500000000000 : ℚ) : ℝ) ≤ stT395o2 217 := by
  have hc : ((67371/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11433599781/500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((67371/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c218 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-133731/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log ((218 : ℕ)) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((218 : ℕ)) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1334509/2500000) (δ := 4969/500000000) (ψ := -555759/1000000) 395 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t218 : ((-90582600141/2500000000000 : ℚ) : ℝ) ≤ stT395o2 218 := by
  have hc : ((-267487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90582600141/2500000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-267487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c219 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-497377/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log ((219 : ℕ)) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((219 : ℕ)) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3798891/5000000) (δ := 1993/200000000) (ψ := -555759/1000000) 395 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t219 : ((-84028358169/1250000000000 : ℚ) : ℝ) ≤ stT395o2 219 := by
  have hc : ((-248701/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84028358169/1250000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-248701/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c220 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-87331/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log ((220 : ℕ)) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((220 : ℕ)) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1172151/2000000) (δ := 2493/250000000) (ψ := -555759/1000000) 395 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t220 : ((-1177655479/25000000000 : ℚ) : ℝ) ≤ stT395o2 220 := by
  have hc : ((-349349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1177655479/25000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-349349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c221 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((30473/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log ((221 : ℕ)) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((221 : ℕ)) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7243/20000) (δ := 2493/250000000) (ψ := -555759/1000000) 395 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t221 : ((1280620341/156250000000 : ℚ) : ℝ) ≤ stT395o2 221 := by
  have hc : ((60921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1280620341/156250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((60921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c222 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((848863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log ((222 : ℕ)) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((222 : ℕ)) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -43513/312500) (δ := 1259/125000000) (ψ := -555759/1000000) 395 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t222 : ((142421484457/2500000000000 : ℚ) : ℝ) ≤ stT395o2 222 := by
  have hc : ((848813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142421484457/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((848813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c223 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((945823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log ((223 : ℕ)) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((223 : ℕ)) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 413347/5000000) (δ := 1259/125000000) (ψ := -555759/1000000) 395 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t223 : ((633335943677/10000000000000 : ℚ) : ℝ) ≤ stT395o2 223 := by
  have hc : ((945773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((633335943677/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((945773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c224 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((69789/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log ((224 : ℕ)) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((224 : ℕ)) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3035879/10000000) (δ := 9931/1000000000) (ψ := -555759/1000000) 395 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t224 : ((46623048187/2000000000000 : ℚ) : ℝ) ≤ stT395o2 224 := by
  have hc : ((69779/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46623048187/2000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((69779/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c225 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-499741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log ((225 : ℕ)) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((225 : ℕ)) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5235239/10000000) (δ := 9931/1000000000) (ψ := -555759/1000000) 395 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t225 : ((-333194166597/10000000000000 : ℚ) : ℝ) ≤ stT395o2 225 := by
  have hc : ((-499791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333194166597/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-499791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c226 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-9853/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log ((226 : ℕ)) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((226 : ℕ)) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3712399/5000000) (δ := 19831/1000000000) (ψ := -555759/1000000) 395 170
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t226 : ((-13108919037/200000000000 : ℚ) : ℝ) ≤ stT395o2 226 := by
  have hc : ((-19707/20000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13108919037/200000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-19707/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c227 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-764649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log ((227 : ℕ)) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((227 : ℕ)) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3051617/5000000) (δ := 9929/1000000000) (ψ := -555759/1000000) 395 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t227 : ((-126887269769/2500000000000 : ℚ) : ℝ) ≤ stT395o2 227 := by
  have hc : ((-764699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126887269769/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-764699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c228 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-1183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log ((228 : ℕ)) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((228 : ℕ)) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3932907/10000000) (δ := 1253/125000000) (ψ := -555759/1000000) 395 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t228 : ((-100002317/625000000000 : ℚ) : ℝ) ≤ stT395o2 228 := by
  have hc : ((-151/62500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100002317/625000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-151/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c229 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((94891/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log ((229 : ℕ)) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((229 : ℕ)) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1772059/10000000) (δ := 9929/1000000000) (ψ := -555759/1000000) 395 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t229 : ((125403101451/2500000000000 : ℚ) : ℝ) ≤ stT395o2 229 := by
  have hc : ((379539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125403101451/2500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((379539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c230 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((988509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log ((230 : ℕ)) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((230 : ℕ)) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 189679/5000000) (δ := 9979/1000000000) (ψ := -555759/1000000) 395 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t230 : ((32588504771/500000000000 : ℚ) : ℝ) ≤ stT395o2 230 := by
  have hc : ((988459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32588504771/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((988459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c231 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((106613/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log ((231 : ℕ)) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((231 : ℕ)) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2521443/10000000) (δ := 9979/1000000000) (ψ := -555759/1000000) 395 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t231 : ((70139550453/2000000000000 : ℚ) : ℝ) ≤ stT395o2 231 := by
  have hc : ((106603/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70139550453/2000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((106603/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c232 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-8963/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log ((232 : ℕ)) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((232 : ℕ)) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 930849/2000000) (δ := 4987/500000000) (ψ := -555759/1000000) 395 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t232 : ((-94168497789/5000000000000 : ℚ) : ℝ) ≤ stT395o2 232 := by
  have hc : ((-143433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94168497789/5000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-143433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c233 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-908787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log ((233 : ℕ)) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((233 : ℕ)) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6777913/10000000) (δ := 1253/125000000) (ψ := -555759/1000000) 395 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t233 : ((-297699556557/5000000000000 : ℚ) : ℝ) ≤ stT395o2 233 := by
  have hc : ((-908837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297699556557/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-908837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c234 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-914953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log ((234 : ℕ)) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((234 : ℕ)) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6815467/10000000) (δ := 9967/1000000000) (ψ := -555759/1000000) 395 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t234 : ((-598156676163/10000000000000 : ℚ) : ℝ) ≤ stT395o2 234 := by
  have hc : ((-915003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-598156676163/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-915003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c235 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-308077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log ((235 : ℕ)) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((235 : ℕ)) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4709919/10000000) (δ := 4993/500000000) (ψ := -555759/1000000) 395 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t235 : ((-201000177783/10000000000000 : ℚ) : ℝ) ≤ stT395o2 235 := by
  have hc : ((-308127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201000177783/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-308127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c236 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((250811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log ((236 : ℕ)) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((236 : ℕ)) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2613309/10000000) (δ := 10017/1000000000) (ψ := -555759/1000000) 395 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t236 : ((1275372203/39062500000 : ℚ) : ℝ) ≤ stT395o2 236 := by
  have hc : ((125393/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1275372203/39062500000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((125393/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c237 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((488991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log ((237 : ℕ)) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((237 : ℕ)) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -262793/5000000) (δ := 10067/1000000000) (ψ := -555759/1000000) 395 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t237 : ((158808577827/2500000000000 : ℚ) : ℝ) ≤ stT395o2 237 := by
  have hc : ((244483/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158808577827/2500000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((244483/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c238 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((813099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log ((238 : ℕ)) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((238 : ℕ)) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1553349/10000000) (δ := 621/62500000) (ψ := -555759/1000000) 395 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t238 : ((527020800947/10000000000000 : ℚ) : ℝ) ≤ stT395o2 238 := by
  have hc : ((813049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((527020800947/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((813049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c239 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((121061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log ((239 : ℕ)) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((239 : ℕ)) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3623593/10000000) (δ := 9967/1000000000) (ψ := -555759/1000000) 395 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t239 : ((39137740653/5000000000000 : ℚ) : ℝ) ≤ stT395o2 239 := by
  have hc : ((121011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39137740653/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((121011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c240 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-25869/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log ((240 : ℕ)) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((240 : ℕ)) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5685197/10000000) (δ := 4943/500000000) (ψ := -555759/1000000) 395 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t240 : ((-8349839379/200000000000 : ℚ) : ℝ) ≤ stT395o2 240 := by
  have hc : ((-25871/40000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8349839379/200000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-25871/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c241 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-62433/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log ((241 : ℕ)) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((241 : ℕ)) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7738209/10000000) (δ := 10067/1000000000) (ψ := -555759/1000000) 395 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t241 : ((-321749335773/5000000000000 : ℚ) : ℝ) ≤ stT395o2 241 := by
  have hc : ((-499489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321749335773/5000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-499489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c242 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-358433/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log ((242 : ℕ)) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((242 : ℕ)) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2962617/5000000) (δ := 9959/1000000000) (ψ := -555759/1000000) 395 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t242 : ((-4608515277/100000000000 : ℚ) : ℝ) ≤ stT395o2 242 := by
  have hc : ((-179229/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4608515277/100000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-179229/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c243 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((15133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log ((243 : ℕ)) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((243 : ℕ)) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3889157/10000000) (δ := 9909/1000000000) (ψ := -555759/1000000) 395 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t243 : ((19351489/20000000000 : ℚ) : ℝ) ≤ stT395o2 243 := by
  have hc : ((15083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19351489/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((15083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c244 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((36769/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log ((244 : ℕ)) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((244 : ℕ)) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -116339/625000) (δ := 2511/250000000) (ψ := -555759/1000000) 395 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t244 : ((5884331259/125000000000 : ℚ) : ℝ) ≤ stT395o2 244 := by
  have hc : ((73533/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5884331259/125000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((73533/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c245 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((249501/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log ((245 : ℕ)) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((245 : ℕ)) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 39497/2500000) (δ := 19909/1000000000) (ψ := -555759/1000000) 395 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t245 : ((79696107463/1250000000000 : ℚ) : ℝ) ≤ stT395o2 245 := by
  have hc : ((498977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79696107463/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((498977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c246 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((646597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log ((246 : ℕ)) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((246 : ℕ)) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 433841/2000000) (δ := 4947/500000000) (ψ := -555759/1000000) 395 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t246 : ((51527856259/1250000000000 : ℚ) : ℝ) ≤ stT395o2 246 := by
  have hc : ((646547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51527856259/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((646547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c247 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-48973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log ((247 : ℕ)) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((247 : ℕ)) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 16689/40000) (δ := 4947/500000000) (ψ := -555759/1000000) 395 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t247 : ((-3117669243/500000000000 : ℚ) : ℝ) ≤ stT395o2 247 := by
  have hc : ((-24499/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3117669243/500000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-24499/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c248 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-390443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log ((248 : ℕ)) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((248 : ℕ)) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6167197/10000000) (δ := 10059/1000000000) (ψ := -555759/1000000) 395 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t248 : ((-61986892617/1250000000000 : ℚ) : ℝ) ≤ stT395o2 248 := by
  have hc : ((-97617/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61986892617/1250000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-97617/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c249 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-992803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log ((249 : ℕ)) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((249 : ℕ)) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3776933/5000000) (δ := 10051/1000000000) (ψ := -555759/1000000) 395 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t249 : ((-25167830697/400000000000 : ℚ) : ℝ) ≤ stT395o2 249 := by
  have hc : ((-992853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25167830697/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-992853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c250 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-306223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log ((250 : ℕ)) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((250 : ℕ)) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5574867/10000000) (δ := 9901/1000000000) (ψ := -555759/1000000) 395 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t250 : ((-3026381017/78125000000 : ℚ) : ℝ) ≤ stT395o2 250 := by
  have hc : ((-38281/62500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3026381017/78125000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-38281/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c251 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((251 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((12891/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55254529/20000000 : ℚ) : ℝ) ≤ Real.log ((251 : ℕ)) / 2 := by
    have h := (log_br_251).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((251 : ℕ)) / 2 ≤ ((5525453/2000000 : ℚ) : ℝ) := by
    have h := (log_br_251).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3603817/10000000) (δ := 9901/1000000000) (ψ := -555759/1000000) 395 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t251 : ((2033391471/250000000000 : ℚ) : ℝ) ≤ stT395o2 251 := by
  have hc : ((6443/50000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((251 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2033391471/250000000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((6443/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c252 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((252 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((24759/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5529429/2000000 : ℚ) : ℝ) ≤ Real.log ((252 : ℕ)) / 2 := by
    have h := (log_br_252).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((252 : ℕ)) / 2 ≤ ((55294291/20000000 : ℚ) : ℝ) := by
    have h := (log_br_252).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -820309/5000000) (δ := 5001/500000000) (ψ := -555759/1000000) 395 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t252 : ((12476560143/250000000000 : ℚ) : ℝ) ≤ stT395o2 252 := by
  have hc : ((396119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((252 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12476560143/250000000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((396119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c253 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((253 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((992081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27666947/10000000 : ℚ) : ℝ) ≤ Real.log ((253 : ℕ)) / 2 := by
    have h := (log_br_253).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((253 : ℕ)) / 2 ≤ ((11066779/4000000 : ℚ) : ℝ) := by
    have h := (log_br_253).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 31483/1000000) (δ := 9951/1000000000) (ψ := -555759/1000000) 395 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t253 : ((311841968757/5000000000000 : ℚ) : ℝ) ≤ stT395o2 253 := by
  have hc : ((992031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((253 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311841968757/5000000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((992031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c254 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((254 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((308831/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27686671/10000000 : ℚ) : ℝ) ≤ Real.log ((254 : ℕ)) / 2 := by
    have h := (log_br_254).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((254 : ℕ)) / 2 ≤ ((55373343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_254).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 90503/400000) (δ := 9951/1000000000) (ψ := -555759/1000000) 395 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t254 : ((19376186873/500000000000 : ℚ) : ℝ) ≤ stT395o2 254 := by
  have hc : ((154403/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((254 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).1
  have hw2 : ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((125491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19376186873/500000000000 : ℚ) : ℝ)
      = ((125491/2000000 : ℚ) : ℝ) * ((154403/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c255 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((255 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-110047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11082527/4000000 : ℚ) : ℝ) ≤ Real.log ((255 : ℕ)) / 2 := by
    have h := (log_br_255).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((255 : ℕ)) / 2 ≤ ((13853159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_255).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4202667/10000000) (δ := 10001/1000000000) (ψ := -555759/1000000) 395 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t255 : ((-2757819753/400000000000 : ℚ) : ℝ) ≤ stT395o2 255 := by
  have hc : ((-110097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((255 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2757819753/400000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-110097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c256 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((256 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-154563/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27725887/10000000 : ℚ) : ℝ) ≤ Real.log ((256 : ℕ)) / 2 := by
    have h := (log_br_256).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((256 : ℕ)) / 2 ≤ ((2218071/800000 : ℚ) : ℝ) := by
    have h := (log_br_256).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1227031/2000000) (δ := 9951/1000000000) (ψ := -555759/1000000) 395 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t256 : ((-96608279573/2000000000000 : ℚ) : ℝ) ≤ stT395o2 256 := by
  have hc : ((-154573/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((256 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96608279573/2000000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-154573/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c257 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((257 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-249151/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1387269/500000 : ℚ) : ℝ) ≤ Real.log ((257 : ℕ)) / 2 := by
    have h := (log_br_257).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((257 : ℕ)) / 2 ≤ ((55490761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_257).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -61183/80000) (δ := 1999/200000000) (ψ := -555759/1000000) 395 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t257 : ((-310847911041/5000000000000 : ℚ) : ℝ) ≤ stT395o2 257 := by
  have hc : ((-498327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((257 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).2
  have h0 : (0:ℝ) ≤ ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310847911041/5000000000000 : ℚ) : ℝ)
      = ((623783/10000000 : ℚ) : ℝ) * ((-498327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c258 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((258 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-82551/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11105919/4000000 : ℚ) : ℝ) ≤ Real.log ((258 : ℕ)) / 2 := by
    have h := (log_br_258).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((258 : ℕ)) / 2 ≤ ((13882399/5000000 : ℚ) : ℝ) := by
    have h := (log_br_258).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5730397/10000000) (δ := 2009/200000000) (ψ := -555759/1000000) 395 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t258 : ((-205591659217/5000000000000 : ℚ) : ℝ) ≤ stT395o2 258 := by
  have hc : ((-330229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((258 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).2
  have h0 : (0:ℝ) ≤ ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205591659217/5000000000000 : ℚ) : ℝ)
      = ((622573/10000000 : ℚ) : ℝ) * ((-330229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c259 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((259 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((42653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1389207/500000 : ℚ) : ℝ) ≤ Real.log ((259 : ℕ)) / 2 := by
    have h := (log_br_259).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((259 : ℕ)) / 2 ≤ ((55568281/20000000 : ℚ) : ℝ) := by
    have h := (log_br_259).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -152813/400000) (δ := 1999/200000000) (ψ := -555759/1000000) 395 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t259 : ((26472183507/10000000000000 : ℚ) : ℝ) ≤ stT395o2 259 := by
  have hc : ((42603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((259 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26472183507/10000000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((42603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c260 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((260 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((143993/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1737713/625000 : ℚ) : ℝ) ≤ Real.log ((260 : ℕ)) / 2 := by
    have h := (log_br_260).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((260 : ℕ)) / 2 ≤ ((55606817/20000000 : ℚ) : ℝ) := by
    have h := (log_br_260).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -191761/1000000) (δ := 1999/200000000) (ψ := -555759/1000000) 395 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t260 : ((89294369059/2000000000000 : ℚ) : ℝ) ≤ stT395o2 260 := by
  have hc : ((143983/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((260 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).1
  have hw2 : ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((620173/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89294369059/2000000000000 : ℚ) : ℝ)
      = ((620173/10000000 : ℚ) : ℝ) * ((143983/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c261 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((261 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((999961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13911301/5000000 : ℚ) : ℝ) ≤ Real.log ((261 : ℕ)) / 2 := by
    have h := (log_br_261).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((261 : ℕ)) / 2 ≤ ((11129041/4000000 : ℚ) : ℝ) := by
    have h := (log_br_261).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -11101/5000000) (δ := 4979/500000000) (ψ := -555759/1000000) 395 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t261 : ((77366113803/1250000000000 : ℚ) : ℝ) ≤ stT395o2 261 := by
  have hc : ((999911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((261 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).1
  have hw2 : ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((77373/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77366113803/1250000000000 : ℚ) : ℝ)
      = ((77373/1250000 : ℚ) : ℝ) * ((999911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c262 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((262 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((91769/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13920861/5000000 : ℚ) : ℝ) ≤ Real.log ((262 : ℕ)) / 2 := by
    have h := (log_br_262).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((262 : ℕ)) / 2 ≤ ((55683447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_262).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1865947/10000000) (δ := 5939/200000000) (ψ := -555759/1000000) 395 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t262 : ((113382420951/2500000000000 : ℚ) : ℝ) ≤ stT395o2 262 := by
  have hc : ((367051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((262 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).1
  have hw2 : ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113382420951/2500000000000 : ℚ) : ℝ)
      = ((308901/5000000 : ℚ) : ℝ) * ((367051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c263 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((263 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((71979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2786077/1000000 : ℚ) : ℝ) ≤ Real.log ((263 : ℕ)) / 2 := by
    have h := (log_br_263).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((263 : ℕ)) / 2 ≤ ((55721541/20000000 : ℚ) : ℝ) := by
    have h := (log_br_263).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 468361/1250000) (δ := 4979/500000000) (ψ := -555759/1000000) 395 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t263 : ((22176645777/5000000000000 : ℚ) : ℝ) ≤ stT395o2 263 := by
  have hc : ((71929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((263 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22176645777/5000000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((71929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c264 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((264 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-15671/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5575949/2000000 : ℚ) : ℝ) ≤ Real.log ((264 : ℕ)) / 2 := by
    have h := (log_br_264).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((264 : ℕ)) / 2 ≤ ((55759493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_264).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2810359/5000000) (δ := 5959/200000000) (ψ := -555759/1000000) 395 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t264 : ((-19291223281/500000000000 : ℚ) : ℝ) ≤ stT395o2 264 := by
  have hc : ((-62689/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((264 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).2
  have h0 : (0:ℝ) ≤ ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19291223281/500000000000 : ℚ) : ℝ)
      = ((307729/5000000 : ℚ) : ℝ) * ((-62689/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c265 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((265 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-989271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27898649/10000000 : ℚ) : ℝ) ≤ Real.log ((265 : ℕ)) / 2 := by
    have h := (log_br_265).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((265 : ℕ)) / 2 ≤ ((55797299/20000000 : ℚ) : ℝ) := by
    have h := (log_br_265).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7487439/10000000) (δ := 1979/200000000) (ψ := -555759/1000000) 395 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t265 : ((-75966991627/1250000000000 : ℚ) : ℝ) ≤ stT395o2 265 := by
  have hc : ((-989321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((265 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).2
  have h0 : (0:ℝ) ≤ ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75966991627/1250000000000 : ℚ) : ℝ)
      = ((76787/1250000 : ℚ) : ℝ) * ((-989321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c266 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((266 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-206719/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55834963/20000000 : ℚ) : ℝ) ≤ Real.log ((266 : ℕ)) / 2 := by
    have h := (log_br_266).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((266 : ℕ)) / 2 ≤ ((13958741/5000000 : ℚ) : ℝ) := by
    have h := (log_br_266).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1272163/2000000) (δ := 4969/500000000) (ψ := -555759/1000000) 395 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t266 : ((-12675535191/250000000000 : ℚ) : ℝ) ≤ stT395o2 266 := by
  have hc : ((-413463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((266 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12675535191/250000000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-413463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c267 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((267 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-230363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27936243/10000000 : ℚ) : ℝ) ≤ Real.log ((267 : ℕ)) / 2 := by
    have h := (log_br_267).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((267 : ℕ)) / 2 ≤ ((55872487/20000000 : ℚ) : ℝ) := by
    have h := (log_br_267).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4508117/10000000) (δ := 2497/250000000) (ψ := -555759/1000000) 395 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t267 : ((-141010682283/10000000000000 : ℚ) : ℝ) ≤ stT395o2 267 := by
  have hc : ((-230413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((267 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141010682283/10000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-230413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c268 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((268 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((484563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55909869/20000000 : ℚ) : ℝ) ≤ Real.log ((268 : ℕ)) / 2 := by
    have h := (log_br_268).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((268 : ℕ)) / 2 ≤ ((5590987/2000000 : ℚ) : ℝ) := by
    have h := (log_br_268).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2662331/10000000) (δ := 1983/200000000) (ψ := -555759/1000000) 395 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t268 : ((295963312511/10000000000000 : ℚ) : ℝ) ≤ stT395o2 268 := by
  have hc : ((484513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((268 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).1
  have hw2 : ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((295963312511/10000000000000 : ℚ) : ℝ)
      = ((610847/10000000 : ℚ) : ℝ) * ((484513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c269 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((269 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((118281/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55947113/20000000 : ℚ) : ℝ) ≤ Real.log ((269 : ℕ)) / 2 := by
    have h := (log_br_269).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((269 : ℕ)) / 2 ≤ ((27973557/10000000 : ℚ) : ℝ) := by
    have h := (log_br_269).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -823409/10000000) (δ := 5019/500000000) (ψ := -555759/1000000) 395 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t269 : ((28845319129/500000000000 : ℚ) : ℝ) ≤ stT395o2 269 := by
  have hc : ((473099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((269 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28845319129/500000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((473099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c270 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((270 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((9197/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55984219/20000000 : ℚ) : ℝ) ≤ Real.log ((270 : ℕ)) / 2 := by
    have h := (log_br_270).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((270 : ℕ)) / 2 ≤ ((2799211/1000000 : ℚ) : ℝ) := by
    have h := (log_br_270).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 10087/100000) (δ := 4969/500000000) (ψ := -555759/1000000) 395 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t270 : ((559680597/10000000000 : ℚ) : ℝ) ≤ stT395o2 270 := by
  have hc : ((18393/20000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((270 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((559680597/10000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((18393/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c271 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((271 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((84677/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14005297/5000000 : ℚ) : ℝ) ≤ Real.log ((271 : ℕ)) / 2 := by
    have h := (log_br_271).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((271 : ℕ)) / 2 ≤ ((56021189/20000000 : ℚ) : ℝ) := by
    have h := (log_br_271).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 566809/2000000) (δ := 2013/200000000) (ψ := -555759/1000000) 395 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t271 : ((1607233661/62500000000 : ℚ) : ℝ) ≤ stT395o2 271 := by
  have hc : ((84667/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((271 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1607233661/62500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((84667/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c272 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((272 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-57239/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2802901/1000000 : ℚ) : ℝ) ≤ Real.log ((272 : ℕ)) / 2 := by
    have h := (log_br_272).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((272 : ℕ)) / 2 ≤ ((56058021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_272).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 37221/80000) (δ := 2013/200000000) (ψ := -555759/1000000) 395 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t272 : ((-1735617933/100000000000 : ℚ) : ℝ) ≤ stT395o2 272 := by
  have hc : ((-57249/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((272 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1735617933/100000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-57249/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c273 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((273 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-849491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56094717/20000000 : ℚ) : ℝ) ≤ Real.log ((273 : ℕ)) / 2 := by
    have h := (log_br_273).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((273 : ℕ)) / 2 ≤ ((28047359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_273).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6464539/10000000) (δ := 1983/200000000) (ψ := -555759/1000000) 395 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t273 : ((-128541500087/2500000000000 : ℚ) : ℝ) ≤ stT395o2 273 := by
  have hc : ((-849541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((273 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128541500087/2500000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-849541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c274 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((274 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-493097/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56131281/20000000 : ℚ) : ℝ) ≤ Real.log ((274 : ℕ)) / 2 := by
    have h := (log_br_274).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((274 : ℕ)) / 2 ≤ ((28065641/10000000 : ℚ) : ℝ) := by
    have h := (log_br_274).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7438077/10000000) (δ := 9931/1000000000) (ψ := -555759/1000000) 395 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t274 : ((-148953171003/2500000000000 : ℚ) : ℝ) ≤ stT395o2 274 := by
  have hc : ((-246561/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((274 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148953171003/2500000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-246561/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c275 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((275 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-632643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5616771/2000000 : ℚ) : ℝ) ≤ Real.log ((275 : ℕ)) / 2 := by
    have h := (log_br_275).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((275 : ℕ)) / 2 ≤ ((56167711/20000000 : ℚ) : ℝ) := by
    have h := (log_br_275).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1127879/2000000) (δ := 9881/1000000000) (ψ := -555759/1000000) 395 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t275 : ((-381528430939/10000000000000 : ℚ) : ℝ) ≤ stT395o2 275 := by
  have hc : ((-632693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((275 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-381528430939/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-632693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c276 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((276 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((31919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7025501/2500000 : ℚ) : ℝ) ≤ Real.log ((276 : ℕ)) / 2 := by
    have h := (log_br_276).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((276 : ℕ)) / 2 ≤ ((56204009/20000000 : ℚ) : ℝ) := by
    have h := (log_br_276).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3847181/10000000) (δ := 2493/250000000) (ψ := -555759/1000000) 395 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t276 : ((19182875301/10000000000000 : ℚ) : ℝ) ≤ stT395o2 276 := by
  have hc : ((31869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((276 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19182875301/10000000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((31869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c277 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((277 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((67887/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2249607/800000 : ℚ) : ℝ) ≤ Real.log ((277 : ℕ)) / 2 := by
    have h := (log_br_277).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((277 : ℕ)) / 2 ≤ ((3515011/1250000 : ℚ) : ℝ) := by
    have h := (log_br_277).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -515359/2500000) (δ := 10031/1000000000) (ψ := -555759/1000000) 395 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t277 : ((20393144381/500000000000 : ℚ) : ℝ) ≤ stT395o2 277 := by
  have hc : ((33941/50000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((277 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20393144381/500000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((33941/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c278 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((278 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((496819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56276211/20000000 : ℚ) : ℝ) ≤ Real.log ((278 : ℕ)) / 2 := by
    have h := (log_br_278).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((278 : ℕ)) / 2 ≤ ((14069053/5000000 : ℚ) : ℝ) := by
    have h := (log_br_278).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -141079/5000000) (δ := 4961/500000000) (ψ := -555759/1000000) 395 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t278 : ((1862232309/31250000000 : ℚ) : ℝ) ≤ stT395o2 278 := by
  have hc : ((248397/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((278 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1862232309/31250000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((248397/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c279 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((279 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((82743/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56312117/20000000 : ℚ) : ℝ) ≤ Real.log ((279 : ℕ)) / 2 := by
    have h := (log_br_279).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((279 : ℕ)) / 2 ≤ ((28156059/10000000 : ℚ) : ℝ) := by
    have h := (log_br_279).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1490701/10000000) (δ := 5011/500000000) (ψ := -555759/1000000) 395 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t279 : ((6191739599/125000000000 : ℚ) : ℝ) ≤ stT395o2 279 := by
  have hc : ((41369/50000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((279 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6191739599/125000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((41369/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c280 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((280 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((16543/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7043487/2500000 : ℚ) : ℝ) ≤ Real.log ((280 : ℕ)) / 2 := by
    have h := (log_br_280).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((280 : ℕ)) / 2 ≤ ((56347897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_280).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3257289/10000000) (δ := 2493/250000000) (ψ := -555759/1000000) 395 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t280 : ((39537843433/2500000000000 : ℚ) : ℝ) ≤ stT395o2 280 := by
  have hc : ((132319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((280 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).1
  have hw2 : ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39537843433/2500000000000 : ℚ) : ℝ)
      = ((298807/5000000 : ℚ) : ℝ) * ((132319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c281 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((281 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-84501/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28191773/10000000 : ℚ) : ℝ) ≤ Real.log ((281 : ℕ)) / 2 := by
    have h := (log_br_281).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((281 : ℕ)) / 2 ≤ ((56383547/20000000 : ℚ) : ℝ) := by
    have h := (log_br_281).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1254377/2500000) (δ := 1259/125000000) (ψ := -555759/1000000) 395 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t281 : ((-1008300741/40000000000 : ℚ) : ℝ) ≤ stT395o2 281 := by
  have hc : ((-84511/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((281 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1008300741/40000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-84511/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c282 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((282 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-181543/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5641907/2000000 : ℚ) : ℝ) ≤ Real.log ((282 : ℕ)) / 2 := by
    have h := (log_br_282).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((282 : ℕ)) / 2 ≤ ((56419071/20000000 : ℚ) : ℝ) := by
    have h := (log_br_282).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1354301/2000000) (δ := 9881/1000000000) (ψ := -555759/1000000) 395 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t282 : ((-27028339769/500000000000 : ℚ) : ℝ) ≤ stT395o2 282 := by
  have hc : ((-181553/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((282 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).2
  have h0 : (0:ℝ) ≤ ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27028339769/500000000000 : ℚ) : ℝ)
      = ((148873/2500000 : ℚ) : ℝ) * ((-181553/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c283 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((283 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-964799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14113617/5000000 : ℚ) : ℝ) ≤ Real.log ((283 : ℕ)) / 2 := by
    have h := (log_br_283).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((283 : ℕ)) / 2 ≤ ((56454469/20000000 : ℚ) : ℝ) := by
    have h := (log_br_283).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3594341/5000000) (δ := 9879/1000000000) (ψ := -555759/1000000) 395 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t283 : ((-573543874711/10000000000000 : ℚ) : ℝ) ≤ stT395o2 283 := by
  have hc : ((-964849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((283 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).2
  have h0 : (0:ℝ) ≤ ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-573543874711/10000000000000 : ℚ) : ℝ)
      = ((594439/10000000 : ℚ) : ℝ) * ((-964849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c284 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((284 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-571239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28244871/10000000 : ℚ) : ℝ) ≤ Real.log ((284 : ℕ)) / 2 := by
    have h := (log_br_284).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((284 : ℕ)) / 2 ≤ ((56489743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_284).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1361757/2500000) (δ := 9979/1000000000) (ψ := -555759/1000000) 395 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t284 : ((-338997750999/10000000000000 : ℚ) : ℝ) ≤ stT395o2 284 := by
  have hc : ((-571289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((284 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-338997750999/10000000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-571289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c285 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((285 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((86071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56524891/20000000 : ℚ) : ℝ) ≤ Real.log ((285 : ℕ)) / 2 := by
    have h := (log_br_285).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((285 : ℕ)) / 2 ≤ ((14131223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_285).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1855773/5000000) (δ := 10029/1000000000) (ψ := -555759/1000000) 395 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t285 : ((12738591827/2500000000000 : ℚ) : ℝ) ≤ stT395o2 285 := by
  have hc : ((86021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((285 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12738591827/2500000000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((86021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c286 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((286 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((175457/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28279959/10000000 : ℚ) : ℝ) ≤ Real.log ((286 : ℕ)) / 2 := by
    have h := (log_br_286).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((286 : ℕ)) / 2 ≤ ((56559919/20000000 : ℚ) : ℝ) := by
    have h := (log_br_286).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -247761/1250000) (δ := 9979/1000000000) (ψ := -555759/1000000) 395 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t286 : ((12967804773/312500000000 : ℚ) : ℝ) ≤ stT395o2 286 := by
  have hc : ((350889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((286 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).1
  have hw2 : ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((36957/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12967804773/312500000000 : ℚ) : ℝ)
      = ((36957/625000 : ℚ) : ℝ) * ((350889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c287 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((287 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((994651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28297411/10000000 : ℚ) : ℝ) ≤ Real.log ((287 : ℕ)) / 2 := by
    have h := (log_br_287).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((287 : ℕ)) / 2 ≤ ((56594823/20000000 : ℚ) : ℝ) := by
    have h := (log_br_287).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -258703/10000000) (δ := 9979/1000000000) (ψ := -555759/1000000) 395 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t287 : ((587094072881/10000000000000 : ℚ) : ℝ) ≤ stT395o2 287 := by
  have hc : ((994601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((287 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).1
  have hw2 : ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((590281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((587094072881/10000000000000 : ℚ) : ℝ)
      = ((590281/10000000 : ℚ) : ℝ) * ((994601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c288 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((288 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((2608/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14157401/5000000 : ℚ) : ℝ) ≤ Real.log ((288 : ℕ)) / 2 := by
    have h := (log_br_288).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((288 : ℕ)) / 2 ≤ ((11325921/4000000 : ℚ) : ℝ) := by
    have h := (log_br_288).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 729329/5000000) (δ := 9879/1000000000) (ψ := -555759/1000000) 395 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t288 : ((9834783801/200000000000 : ℚ) : ℝ) ≤ stT395o2 288 := by
  have hc : ((83451/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((288 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9834783801/200000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((83451/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c289 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((289 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((59631/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28332133/10000000 : ℚ) : ℝ) ≤ Real.log ((289 : ℕ)) / 2 := by
    have h := (log_br_289).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((289 : ℕ)) / 2 ≤ ((56664267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_289).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1585047/5000000) (δ := 4987/500000000) (ψ := -555759/1000000) 395 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t289 : ((7014231787/400000000000 : ℚ) : ℝ) ≤ stT395o2 289 := by
  have hc : ((59621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((289 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7014231787/400000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((59621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c290 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((290 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-46303/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56698809/20000000 : ℚ) : ℝ) ≤ Real.log ((290 : ℕ)) / 2 := by
    have h := (log_br_290).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((290 : ℕ)) / 2 ≤ ((5669881/2000000 : ℚ) : ℝ) := by
    have h := (log_br_290).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 975131/2000000) (δ := 9929/1000000000) (ψ := -555759/1000000) 395 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t290 : ((-108775056377/5000000000000 : ℚ) : ℝ) ≤ stT395o2 290 := by
  have hc : ((-185237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((290 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108775056377/5000000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-185237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c291 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((291 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-872023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3545827/1250000 : ℚ) : ℝ) ≤ Real.log ((291 : ℕ)) / 2 := by
    have h := (log_br_291).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((291 : ℕ)) / 2 ≤ ((56733233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_291).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 657529/1000000) (δ := 5037/500000000) (ψ := -555759/1000000) 395 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t291 : ((-511218785403/10000000000000 : ℚ) : ℝ) ≤ stT395o2 291 := by
  have hc : ((-872073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((291 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).2
  have h0 : (0:ℝ) ≤ ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-511218785403/10000000000000 : ℚ) : ℝ)
      = ((586211/10000000 : ℚ) : ℝ) * ((-872073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c292 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((292 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-986243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28383769/10000000 : ℚ) : ℝ) ≤ Real.log ((292 : ℕ)) / 2 := by
    have h := (log_br_292).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((292 : ℕ)) / 2 ≤ ((56767539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_292).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3719407/5000000) (δ := 9887/1000000000) (ψ := -555759/1000000) 395 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t292 : ((-288592290679/5000000000000 : ℚ) : ℝ) ≤ stT395o2 292 := by
  have hc : ((-986293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((292 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-288592290679/5000000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-986293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c293 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((293 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-666509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28400863/10000000 : ℚ) : ℝ) ≤ Real.log ((293 : ℕ)) / 2 := by
    have h := (log_br_293).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((293 : ℕ)) / 2 ≤ ((56801727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_293).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2875391/5000000) (δ := 5033/500000000) (ψ := -555759/1000000) 395 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t293 : ((-389408433713/10000000000000 : ℚ) : ℝ) ≤ stT395o2 293 := by
  have hc : ((-666559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((293 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-389408433713/10000000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-666559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c294 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((294 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-7073/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56835797/20000000 : ℚ) : ℝ) ≤ Real.log ((294 : ℕ)) / 2 := by
    have h := (log_br_294).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((294 : ℕ)) / 2 ≤ ((28417899/10000000 : ℚ) : ℝ) := by
    have h := (log_br_294).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2034263/5000000) (δ := 2479/250000000) (ψ := -555759/1000000) 395 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t294 : ((-4128703551/1250000000000 : ℚ) : ℝ) ≤ stT395o2 294 := by
  have hc : ((-28317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((294 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4128703551/1250000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-28317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c295 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((295 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((115231/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56869753/20000000 : ℚ) : ℝ) ≤ Real.log ((295 : ℕ)) / 2 := by
    have h := (log_br_295).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((295 : ℕ)) / 2 ≤ ((28434877/10000000 : ℚ) : ℝ) := by
    have h := (log_br_295).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -597987/2500000) (δ := 10037/1000000000) (ψ := -555759/1000000) 395 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t295 : ((33542100531/1000000000000 : ℚ) : ℝ) ≤ stT395o2 295 := by
  have hc : ((115221/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((295 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33542100531/1000000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((115221/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c296 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((296 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((191739/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28451797/10000000 : ℚ) : ℝ) ≤ Real.log ((296 : ℕ)) / 2 := by
    have h := (log_br_296).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((296 : ℕ)) / 2 ≤ ((11380719/4000000 : ℚ) : ℝ) := by
    have h := (log_br_296).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -721049/10000000) (δ := 9887/1000000000) (ψ := -555759/1000000) 395 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t296 : ((55720090251/1000000000000 : ℚ) : ℝ) ≤ stT395o2 296 := by
  have hc : ((191729/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((296 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55720090251/1000000000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((191729/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c297 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((297 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((929519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56937321/20000000 : ℚ) : ℝ) ≤ Real.log ((297 : ℕ)) / 2 := by
    have h := (log_br_297).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((297 : ℕ)) / 2 ≤ ((28468661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_297).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 472111/5000000) (δ := 10037/1000000000) (ψ := -555759/1000000) 395 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t297 : ((269665911501/5000000000000 : ℚ) : ℝ) ≤ stT395o2 297 := by
  have hc : ((929469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((297 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((269665911501/5000000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((929469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c298 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((298 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((504887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28485467/10000000 : ℚ) : ℝ) ≤ Real.log ((298 : ℕ)) / 2 := by
    have h := (log_br_298).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((298 : ℕ)) / 2 ≤ ((11394187/4000000 : ℚ) : ℝ) := by
    have h := (log_br_298).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2603863/10000000) (δ := 5033/500000000) (ψ := -555759/1000000) 395 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t298 : ((73110999177/2500000000000 : ℚ) : ℝ) ≤ stT395o2 298 := by
  have hc : ((504837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((298 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73110999177/2500000000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((504837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c299 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((299 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-132007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11400887/4000000 : ℚ) : ℝ) ≤ Real.log ((299 : ℕ)) / 2 := by
    have h := (log_br_299).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((299 : ℕ)) / 2 ≤ ((14251109/5000000 : ℚ) : ℝ) := by
    have h := (log_br_299).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 170319/400000) (δ := 313/31250000) (ψ := -555759/1000000) 395 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t299 : ((-15274108791/2000000000000 : ℚ) : ℝ) ≤ stT395o2 299 := by
  have hc : ((-132057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((299 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15274108791/2000000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-132057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c300 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((300 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-355819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((222804/78125 : ℚ) : ℝ) ≤ Real.log ((300 : ℕ)) / 2 := by
    have h := (log_br_300).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((300 : ℕ)) / 2 ≤ ((2281513/800000 : ℚ) : ℝ) := by
    have h := (log_br_300).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5906557/10000000) (δ := 4983/500000000) (ψ := -555759/1000000) 395 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t300 : ((-51361722311/1250000000000 : ℚ) : ℝ) ≤ stT395o2 300 := by
  have hc : ((-88961/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((300 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51361722311/1250000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-88961/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c301 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((301 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-4963/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28535551/10000000 : ℚ) : ℝ) ≤ Real.log ((301 : ℕ)) / 2 := by
    have h := (log_br_301).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((301 : ℕ)) / 2 ≤ ((57071103/20000000 : ℚ) : ℝ) := by
    have h := (log_br_301).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3774829/5000000) (δ := 5033/500000000) (ψ := -555759/1000000) 395 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t301 : ((-11443090523/200000000000 : ℚ) : ℝ) ≤ stT395o2 301 := by
  have hc : ((-19853/20000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((301 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11443090523/200000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-19853/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c302 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((302 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-430557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5710427/2000000 : ℚ) : ℝ) ≤ Real.log ((302 : ℕ)) / 2 := by
    have h := (log_br_302).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((302 : ℕ)) / 2 ≤ ((57104271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_302).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1304127/2000000) (δ := 9959/1000000000) (ψ := -555759/1000000) 395 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t302 : ((-30971547969/625000000000 : ℚ) : ℝ) ≤ stT395o2 302 := by
  have hc : ((-215291/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((302 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30971547969/625000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-215291/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c303 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((303 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-375153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3571083/1250000 : ℚ) : ℝ) ≤ Real.log ((303 : ℕ)) / 2 := by
    have h := (log_br_303).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((303 : ℕ)) / 2 ≤ ((57137329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_303).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1222099/2500000) (δ := 4947/500000000) (ψ := -555759/1000000) 395 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t303 : ((-43109699091/2000000000000 : ℚ) : ℝ) ≤ stT395o2 303 := by
  have hc : ((-375203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((303 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43109699091/2000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-375203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c304 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((304 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((263049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57170277/20000000 : ℚ) : ℝ) ≤ Real.log ((304 : ℕ)) / 2 := by
    have h := (log_br_304).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((304 : ℕ)) / 2 ≤ ((28585139/10000000 : ℚ) : ℝ) := by
    have h := (log_br_304).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3261539/10000000) (δ := 1243/125000000) (ψ := -555759/1000000) 395 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t304 : ((150840183461/10000000000000 : ℚ) : ℝ) ≤ stT395o2 304 := by
  have hc : ((262999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((304 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).1
  have hw2 : ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150840183461/10000000000000 : ℚ) : ℝ)
      = ((573539/10000000 : ℚ) : ℝ) * ((262999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c305 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((305 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((792423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57203117/20000000 : ℚ) : ℝ) ≤ Real.log ((305 : ℕ)) / 2 := by
    have h := (log_br_305).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((305 : ℕ)) / 2 ≤ ((28601559/10000000 : ℚ) : ℝ) := by
    have h := (log_br_305).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -12813/78125) (δ := 1243/125000000) (ψ := -555759/1000000) 395 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t305 : ((226855597527/5000000000000 : ℚ) : ℝ) ≤ stT395o2 305 := by
  have hc : ((792373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((305 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226855597527/5000000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((792373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c306 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((306 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((199991/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57235851/20000000 : ℚ) : ℝ) ≤ Real.log ((306 : ℕ)) / 2 := by
    have h := (log_br_306).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((306 : ℕ)) / 2 ≤ ((14308963/5000000 : ℚ) : ℝ) := by
    have h := (log_br_306).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -23823/10000000) (δ := 9909/1000000000) (ψ := -555759/1000000) 395 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t306 : ((114321338441/2000000000000 : ℚ) : ℝ) ≤ stT395o2 306 := by
  have hc : ((199981/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((306 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114321338441/2000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((199981/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c307 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((307 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((80517/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57268477/20000000 : ℚ) : ℝ) ≤ Real.log ((307 : ℕ)) / 2 := by
    have h := (log_br_307).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((307 : ℕ)) / 2 ≤ ((28634239/10000000 : ℚ) : ℝ) := by
    have h := (log_br_307).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 793543/5000000) (δ := 1243/125000000) (ψ := -555759/1000000) 395 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t307 : ((35898917/781250000 : ℚ) : ℝ) ≤ stT395o2 307 := by
  have hc : ((2516/3125 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((307 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35898917/781250000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((2516/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c308 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((308 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((18093/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57300997/20000000 : ℚ) : ℝ) ≤ Real.log ((308 : ℕ)) / 2 := by
    have h := (log_br_308).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((308 : ℕ)) / 2 ≤ ((28650499/10000000 : ℚ) : ℝ) := by
    have h := (log_br_308).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3192761/10000000) (δ := 1243/125000000) (ψ := -555759/1000000) 395 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t308 : ((41230587819/2500000000000 : ℚ) : ℝ) ≤ stT395o2 308 := by
  have hc : ((144719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((308 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41230587819/2500000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((144719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c309 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((309 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-84903/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14333353/5000000 : ℚ) : ℝ) ≤ Real.log ((309 : ℕ)) / 2 := by
    have h := (log_br_309).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((309 : ℕ)) / 2 ≤ ((57333413/20000000 : ℚ) : ℝ) := by
    have h := (log_br_309).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4793251/10000000) (δ := 10059/1000000000) (ψ := -555759/1000000) 395 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t309 : ((-96613629111/5000000000000 : ℚ) : ℝ) ≤ stT395o2 309 := by
  have hc : ((-169831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((309 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96613629111/5000000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-169831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c310 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((310 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-416533/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28682861/10000000 : ℚ) : ℝ) ≤ Real.log ((310 : ℕ)) / 2 := by
    have h := (log_br_310).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((310 : ℕ)) / 2 ≤ ((57365723/20000000 : ℚ) : ℝ) := by
    have h := (log_br_310).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3194279/5000000) (δ := 4997/500000000) (ψ := -555759/1000000) 395 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t310 : ((-59147278699/1250000000000 : ℚ) : ℝ) ≤ stT395o2 310 := by
  have hc : ((-208279/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((310 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59147278699/1250000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-208279/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c311 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((311 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-499377/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57397929/20000000 : ℚ) : ℝ) ≤ Real.log ((311 : ℕ)) / 2 := by
    have h := (log_br_311).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((311 : ℕ)) / 2 ≤ ((5739793/2000000 : ℚ) : ℝ) := by
    have h := (log_br_311).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1545837/2000000) (δ := 4951/500000000) (ψ := -555759/1000000) 395 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t311 : ((-17699056581/312500000000 : ℚ) : ℝ) ≤ stT395o2 311 := by
  have hc : ((-249701/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((311 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17699056581/312500000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-249701/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c312 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((312 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-387547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57430031/20000000 : ℚ) : ℝ) ≤ Real.log ((312 : ℕ)) / 2 := by
    have h := (log_br_312).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((312 : ℕ)) / 2 ≤ ((3589377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_312).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6144149/10000000) (δ := 5001/500000000) (ψ := -555759/1000000) 395 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t312 : ((-54854906127/1250000000000 : ℚ) : ℝ) ≤ stT395o2 312 := by
  have hc : ((-96893/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((312 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54854906127/1250000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-96893/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c313 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((313 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-252113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57462031/20000000 : ℚ) : ℝ) ≤ Real.log ((313 : ℕ)) / 2 := by
    have h := (log_br_313).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((313 : ℕ)) / 2 ≤ ((3591377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_313).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4564149/10000000) (δ := 5001/500000000) (ψ := -555759/1000000) 395 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t313 : ((-71265550571/5000000000000 : ℚ) : ℝ) ≤ stT395o2 313 := by
  have hc : ((-252163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((313 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71265550571/5000000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-252163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c314 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((314 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((183193/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57493929/20000000 : ℚ) : ℝ) ≤ Real.log ((314 : ℕ)) / 2 := by
    have h := (log_br_314).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((314 : ℕ)) / 2 ≤ ((5749393/2000000 : ℚ) : ℝ) := by
    have h := (log_br_314).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -597837/2000000) (δ := 4951/500000000) (ψ := -555759/1000000) 395 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t314 : ((201889773/9765625000 : ℚ) : ℝ) ≤ stT395o2 314 := by
  have hc : ((5724/15625 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((314 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201889773/9765625000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((5724/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c315 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((315 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((843149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28762863/10000000 : ℚ) : ℝ) ≤ Real.log ((315 : ℕ)) / 2 := by
    have h := (log_br_315).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((315 : ℕ)) / 2 ≤ ((57525727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_315).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -177401/1250000) (δ := 9901/1000000000) (ψ := -555759/1000000) 395 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t315 : ((118758082041/2500000000000 : ℚ) : ℝ) ≤ stT395o2 315 := by
  have hc : ((843099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((315 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118758082041/2500000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((843099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c316 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((316 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((9983/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28778711/10000000 : ℚ) : ℝ) ≤ Real.log ((316 : ℕ)) / 2 := by
    have h := (log_br_316).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((316 : ℕ)) / 2 ≤ ((57557423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_316).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 72891/5000000) (δ := 9901/1000000000) (ψ := -555759/1000000) 395 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t316 : ((2246234199/40000000000 : ℚ) : ℝ) ≤ stT395o2 316 := by
  have hc : ((3993/4000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((316 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2246234199/40000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((3993/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c317 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((317 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((194029/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57589017/20000000 : ℚ) : ℝ) ≤ Real.log ((317 : ℕ)) / 2 := by
    have h := (log_br_317).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((317 : ℕ)) / 2 ≤ ((28794509/10000000 : ℚ) : ℝ) := by
    have h := (log_br_317).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 341157/2000000) (δ := 4951/500000000) (ψ := -555759/1000000) 395 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t317 : ((43588134923/1000000000000 : ℚ) : ℝ) ≤ stT395o2 317 := by
  have hc : ((388033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((317 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43588134923/1000000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((388033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c318 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((318 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((52659/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57620513/20000000 : ℚ) : ℝ) ≤ Real.log ((318 : ℕ)) / 2 := by
    have h := (log_br_318).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((318 : ℕ)) / 2 ≤ ((28810257/10000000 : ℚ) : ℝ) := by
    have h := (log_br_318).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 32609/100000) (δ := 4951/500000000) (ψ := -555759/1000000) 395 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t318 : ((7381021257/500000000000 : ℚ) : ℝ) ≤ stT395o2 318 := by
  have hc : ((52649/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((318 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7381021257/500000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((52649/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c319 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((319 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-346347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57651911/20000000 : ℚ) : ℝ) ≤ Real.log ((319 : ℕ)) / 2 := by
    have h := (log_br_319).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((319 : ℕ)) / 2 ≤ ((7206489/2500000 : ℚ) : ℝ) := by
    have h := (log_br_319).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 601397/1250000) (δ := 5001/500000000) (ψ := -555759/1000000) 395 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t319 : ((-193945255521/10000000000000 : ℚ) : ℝ) ≤ stT395o2 319 := by
  have hc : ((-346397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((319 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193945255521/10000000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-346397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c320 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((320 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-825907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57683209/20000000 : ℚ) : ℝ) ≤ Real.log ((320 : ℕ)) / 2 := by
    have h := (log_br_320).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((320 : ℕ)) / 2 ≤ ((5768321/2000000 : ℚ) : ℝ) := by
    have h := (log_br_320).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1271303/2000000) (δ := 4951/500000000) (ψ := -555759/1000000) 395 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t320 : ((-461724004269/10000000000000 : ℚ) : ℝ) ≤ stT395o2 320 := by
  have hc : ((-825957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((320 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-461724004269/10000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-825957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c321 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((321 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-999851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57714411/20000000 : ℚ) : ℝ) ≤ Real.log ((321 : ℕ)) / 2 := by
    have h := (log_br_321).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((321 : ℕ)) / 2 ≤ ((14428603/5000000 : ℚ) : ℝ) := by
    have h := (log_br_321).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7810849/10000000) (δ := 5029/500000000) (ψ := -555759/1000000) 395 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t321 : ((-279045371773/5000000000000 : ℚ) : ℝ) ≤ stT395o2 321 := by
  have hc : ((-999901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((321 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279045371773/5000000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-999901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c322 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((322 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-807109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11549103/4000000 : ℚ) : ℝ) ≤ Real.log ((322 : ℕ)) / 2 := by
    have h := (log_br_322).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((322 : ℕ)) / 2 ≤ ((14436379/5000000 : ℚ) : ℝ) := by
    have h := (log_br_322).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6275089/10000000) (δ := 5029/500000000) (ψ := -555759/1000000) 395 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t322 : ((-449812760361/10000000000000 : ℚ) : ℝ) ≤ stT395o2 322 := by
  have hc : ((-807159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((322 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-449812760361/10000000000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-807159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c323 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((323 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-80261/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57776523/20000000 : ℚ) : ℝ) ≤ Real.log ((323 : ℕ)) / 2 := by
    have h := (log_br_323).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((323 : ℕ)) / 2 ≤ ((14444131/5000000 : ℚ) : ℝ) := by
    have h := (log_br_323).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4744069/10000000) (δ := 5029/500000000) (ψ := -555759/1000000) 395 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t323 : ((-17866151801/1000000000000 : ℚ) : ℝ) ≤ stT395o2 323 := by
  have hc : ((-160547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((323 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17866151801/1000000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-160547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c324 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((324 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((279891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11561487/4000000 : ℚ) : ℝ) ≤ Real.log ((324 : ℕ)) / 2 := by
    have h := (log_br_324).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((324 : ℕ)) / 2 ≤ ((14451859/5000000 : ℚ) : ℝ) := by
    have h := (log_br_324).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3217789/10000000) (δ := 5029/500000000) (ψ := -555759/1000000) 395 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t324 : ((31093413351/2000000000000 : ℚ) : ℝ) ≤ stT395o2 324 := by
  have hc : ((279841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((324 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31093413351/2000000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((279841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c325 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((325 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((155703/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57838251/20000000 : ℚ) : ℝ) ≤ Real.log ((325 : ℕ)) / 2 := by
    have h := (log_br_325).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((325 : ℕ)) / 2 ≤ ((14459563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_325).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1696249/10000000) (δ := 5029/500000000) (ψ := -555759/1000000) 395 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t325 : ((863629071/20000000000 : ℚ) : ℝ) ≤ stT395o2 325 := by
  have hc : ((155693/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((325 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((863629071/20000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((155693/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c326 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((326 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((249357/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57868973/20000000 : ℚ) : ℝ) ≤ Real.log ((326 : ℕ)) / 2 := by
    have h := (log_br_326).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((326 : ℕ)) / 2 ≤ ((28934487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_326).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -179351/10000000) (δ := 1999/200000000) (ψ := -555759/1000000) 395 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t326 : ((34524738159/625000000000 : ℚ) : ℝ) ≤ stT395o2 326 := by
  have hc : ((498689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((326 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34524738159/625000000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((498689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c327 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((327 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((215301/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57899601/20000000 : ℚ) : ℝ) ≤ Real.log ((327 : ℕ)) / 2 := by
    have h := (log_br_327).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((327 : ℕ)) / 2 ≤ ((28949801/10000000 : ℚ) : ℝ) := by
    have h := (log_br_327).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1332907/10000000) (δ := 4979/500000000) (ψ := -555759/1000000) 395 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t327 : ((238109511577/5000000000000 : ℚ) : ℝ) ≤ stT395o2 327 := by
  have hc : ((430577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((327 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238109511577/5000000000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((430577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c328 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((328 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((210509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7241267/2500000 : ℚ) : ℝ) ≤ Real.log ((328 : ℕ)) / 2 := by
    have h := (log_br_328).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((328 : ℕ)) / 2 ≤ ((57930137/20000000 : ℚ) : ℝ) := by
    have h := (log_br_328).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 710143/2500000) (δ := 2009/200000000) (ψ := -555759/1000000) 395 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t328 : ((29055053497/1250000000000 : ℚ) : ℝ) ≤ stT395o2 328 := by
  have hc : ((52621/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((328 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29055053497/1250000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((52621/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c329 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((329 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-10367/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57960577/20000000 : ℚ) : ℝ) ≤ Real.log ((329 : ℕ)) / 2 := by
    have h := (log_br_329).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((329 : ℕ)) / 2 ≤ ((28980289/10000000 : ℚ) : ℝ) := by
    have h := (log_br_329).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4343597/10000000) (δ := 4979/500000000) (ψ := -555759/1000000) 395 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t329 : ((-22868946299/2500000000000 : ℚ) : ℝ) ≤ stT395o2 329 := by
  have hc : ((-82961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((329 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22868946299/2500000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-82961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c330 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((330 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-693283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28995463/10000000 : ℚ) : ℝ) ≤ Real.log ((330 : ℕ)) / 2 := by
    have h := (log_br_330).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((330 : ℕ)) / 2 ≤ ((57990927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_330).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5842079/10000000) (δ := 1251/125000000) (ψ := -555759/1000000) 395 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t330 : ((-190833668253/5000000000000 : ℚ) : ℝ) ≤ stT395o2 330 := by
  have hc : ((-693333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((330 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190833668253/5000000000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-693333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c331 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((331 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-489307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58021183/20000000 : ℚ) : ℝ) ≤ Real.log ((331 : ℕ)) / 2 := by
    have h := (log_br_331).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((331 : ℕ)) / 2 ≤ ((906581/312500 : ℚ) : ℝ) := by
    have h := (log_br_331).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3668009/5000000) (δ := 1979/200000000) (ψ := -555759/1000000) 395 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t331 : ((-1344806669/25000000000 : ℚ) : ℝ) ≤ stT395o2 331 := by
  have hc : ((-122333/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((331 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1344806669/25000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-122333/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c332 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((332 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-925443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58051349/20000000 : ℚ) : ℝ) ≤ Real.log ((332 : ℕ)) / 2 := by
    have h := (log_br_332).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((332 : ℕ)) / 2 ≤ ((1161027/400000 : ℚ) : ℝ) := by
    have h := (log_br_332).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6882499/10000000) (δ := 309/31250000) (ψ := -555759/1000000) 395 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t332 : ((-253965459623/5000000000000 : ℚ) : ℝ) ≤ stT395o2 332 := by
  have hc : ((-925493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((332 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253965459623/5000000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-925493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c333 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((333 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-554883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3630089/1250000 : ℚ) : ℝ) ≤ Real.log ((333 : ℕ)) / 2 := by
    have h := (log_br_333).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((333 : ℕ)) / 2 ≤ ((2323257/800000 : ℚ) : ℝ) := by
    have h := (log_br_333).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2698773/5000000) (δ := 4969/500000000) (ψ := -555759/1000000) 395 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t333 : ((-304101619201/10000000000000 : ℚ) : ℝ) ≤ stT395o2 333 := by
  have hc : ((-554933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((333 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).2
  have h0 : (0:ℝ) ≤ ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304101619201/10000000000000 : ℚ) : ℝ)
      = ((547997/10000000 : ℚ) : ℝ) * ((-554933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c334 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((334 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((1991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58111409/20000000 : ℚ) : ℝ) ≤ Real.log ((334 : ℕ)) / 2 := by
    have h := (log_br_334).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((334 : ℕ)) / 2 ≤ ((5811141/2000000 : ℚ) : ℝ) := by
    have h := (log_br_334).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -979259/2500000) (δ := 2013/200000000) (ψ := -555759/1000000) 395 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t334 : ((21514921/100000000000 : ℚ) : ℝ) ≤ stT395o2 334 := by
  have hc : ((983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((334 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21514921/100000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c335 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((335 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((112007/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11628261/4000000 : ℚ) : ℝ) ≤ Real.log ((335 : ℕ)) / 2 := by
    have h := (log_br_335).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((335 : ℕ)) / 2 ≤ ((29070653/10000000 : ℚ) : ℝ) := by
    have h := (log_br_335).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2440921/10000000) (δ := 2013/200000000) (ψ := -555759/1000000) 395 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t335 : ((30595228463/1000000000000 : ℚ) : ℝ) ≤ stT395o2 335 := by
  have hc : ((111997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((335 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30595228463/1000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((111997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c336 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((336 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((925781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58171111/20000000 : ℚ) : ℝ) ≤ Real.log ((336 : ℕ)) / 2 := by
    have h := (log_br_336).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((336 : ℕ)) / 2 ≤ ((7271389/2500000 : ℚ) : ℝ) := by
    have h := (log_br_336).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3877/40000) (δ := 1993/200000000) (ψ := -555759/1000000) 395 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t336 : ((63128374083/1250000000000 : ℚ) : ℝ) ≤ stT395o2 336 := by
  have hc : ((925731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((336 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63128374083/1250000000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((925731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c337 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((337 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((980219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58200829/20000000 : ℚ) : ℝ) ≤ Real.log ((337 : ℕ)) / 2 := by
    have h := (log_br_337).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((337 : ℕ)) / 2 ≤ ((5820083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_337).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 124519/2500000) (δ := 309/31250000) (ψ := -555759/1000000) 395 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t337 : ((266965690023/5000000000000 : ℚ) : ℝ) ≤ stT395o2 337 := by
  have hc : ((980169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((337 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((266965690023/5000000000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((980169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c338 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((338 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((70781/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29115229/10000000 : ℚ) : ℝ) ≤ Real.log ((338 : ℕ)) / 2 := by
    have h := (log_br_338).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((338 : ℕ)) / 2 ≤ ((58230459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_338).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 122563/625000) (δ := 1983/200000000) (ψ := -555759/1000000) 395 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t338 : ((601516377/15625000000 : ℚ) : ℝ) ≤ stT395o2 338 := by
  have hc : ((8847/12500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((338 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((601516377/15625000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((8847/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c339 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((339 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((201529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58260001/20000000 : ℚ) : ℝ) ≤ Real.log ((339 : ℕ)) / 2 := by
    have h := (log_br_339).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((339 : ℕ)) / 2 ≤ ((29130001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_339).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1709847/5000000) (δ := 2013/200000000) (ψ := -555759/1000000) 395 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t339 : ((175085251/16000000000 : ℚ) : ℝ) ≤ stT395o2 339 := by
  have hc : ((201479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((339 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175085251/16000000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((201479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c340 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((340 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-184911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3643091/1250000 : ℚ) : ℝ) ≤ Real.log ((340 : ℕ)) / 2 := by
    have h := (log_br_340).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((340 : ℕ)) / 2 ≤ ((58289457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_340).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2437017/5000000) (δ := 4969/500000000) (ψ := -555759/1000000) 395 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t340 : ((-12536973259/625000000000 : ℚ) : ℝ) ≤ stT395o2 340 := by
  have hc : ((-23117/62500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((340 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12536973259/625000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-23117/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c341 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((341 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-818523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7289853/2500000 : ℚ) : ℝ) ≤ Real.log ((341 : ℕ)) / 2 := by
    have h := (log_br_341).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((341 : ℕ)) / 2 ≤ ((2332753/800000 : ℚ) : ℝ) := by
    have h := (log_br_341).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6324079/10000000) (δ := 4969/500000000) (ψ := -555759/1000000) 395 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t341 : ((-443282655263/10000000000000 : ℚ) : ℝ) ≤ stT395o2 341 := by
  have hc : ((-818573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((341 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-443282655263/10000000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-818573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c342 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((342 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-199887/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58348107/20000000 : ℚ) : ℝ) ≤ Real.log ((342 : ℕ)) / 2 := by
    have h := (log_br_342).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((342 : ℕ)) / 2 ≤ ((14587027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_342).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7769927/10000000) (δ := 2497/250000000) (ψ := -555759/1000000) 395 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t342 : ((-108092103883/2000000000000 : ℚ) : ℝ) ≤ stT395o2 342 := by
  have hc : ((-199897/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((342 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108092103883/2000000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-199897/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c343 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((343 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-856153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7297163/2500000 : ℚ) : ℝ) ≤ Real.log ((343 : ℕ)) / 2 := by
    have h := (log_br_343).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((343 : ℕ)) / 2 ≤ ((11675461/4000000 : ℚ) : ℝ) := by
    have h := (log_br_343).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3248217/5000000) (δ := 9923/1000000000) (ψ := -555759/1000000) 395 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t343 : ((-9246136197/200000000000 : ℚ) : ℝ) ≤ stT395o2 343 := by
  have hc : ((-856203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((343 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9246136197/200000000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-856203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c344 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((344 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-437499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3650401/1250000 : ℚ) : ℝ) ≤ Real.log ((344 : ℕ)) / 2 := by
    have h := (log_br_344).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((344 : ℕ)) / 2 ≤ ((58406417/20000000 : ℚ) : ℝ) := by
    have h := (log_br_344).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5059029/10000000) (δ := 9923/1000000000) (ψ := -555759/1000000) 395 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t344 : ((-58977667259/2500000000000 : ℚ) : ℝ) ≤ stT395o2 344 := by
  have hc : ((-437549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((344 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58977667259/2500000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-437549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c345 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((345 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((30049/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14608861/5000000 : ℚ) : ℝ) ≤ Real.log ((345 : ℕ)) / 2 := by
    have h := (log_br_345).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((345 : ℕ)) / 2 ≤ ((11687089/4000000 : ℚ) : ℝ) := by
    have h := (log_br_345).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -906443/2500000) (δ := 1003/100000000) (ψ := -555759/1000000) 395 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t345 : ((32342161813/5000000000000 : ℚ) : ℝ) ≤ stT395o2 345 := by
  have hc : ((60073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((345 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32342161813/5000000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((60073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c346 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((346 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((127633/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58464387/20000000 : ℚ) : ℝ) ≤ Real.log ((346 : ℕ)) / 2 := by
    have h := (log_br_346).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((346 : ℕ)) / 2 ≤ ((14616097/5000000 : ℚ) : ℝ) := by
    have h := (log_br_346).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2196711/10000000) (δ := 247/25000000) (ψ := -555759/1000000) 395 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t346 : ((68610507669/2000000000000 : ℚ) : ℝ) ≤ stT395o2 346 := by
  have hc : ((127623/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((346 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68610507669/2000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((127623/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c347 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((347 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((95273/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58493247/20000000 : ℚ) : ℝ) ≤ Real.log ((347 : ℕ)) / 2 := by
    have h := (log_br_347).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((347 : ℕ)) / 2 ≤ ((913957/312500 : ℚ) : ℝ) := by
    have h := (log_br_347).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -192937/2500000) (δ := 10073/1000000000) (ψ := -555759/1000000) 395 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t347 : ((3196408119/62500000000 : ℚ) : ℝ) ≤ stT395o2 347 := by
  have hc : ((23817/25000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((347 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3196408119/62500000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((23817/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c348 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((348 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((966481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7315253/2500000 : ℚ) : ℝ) ≤ Real.log ((348 : ℕ)) / 2 := by
    have h := (log_br_348).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((348 : ℕ)) / 2 ≤ ((2340881/800000 : ℚ) : ℝ) := by
    have h := (log_br_348).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 162279/2500000) (δ := 9923/1000000000) (ψ := -555759/1000000) 395 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t348 : ((64757642017/1250000000000 : ℚ) : ℝ) ≤ stT395o2 348 := by
  have hc : ((966431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((348 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64757642017/1250000000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((966431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c349 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((349 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((169387/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58550719/20000000 : ℚ) : ℝ) ≤ Real.log ((349 : ℕ)) / 2 := by
    have h := (log_br_349).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((349 : ℕ)) / 2 ≤ ((182971/62500 : ℚ) : ℝ) := by
    have h := (log_br_349).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 516483/2500000) (δ := 10073/1000000000) (ψ := -555759/1000000) 395 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t349 : ((181327935963/5000000000000 : ℚ) : ℝ) ≤ stT395o2 349 := by
  have hc : ((338749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((349 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181327935963/5000000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((338749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c350 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((350 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((178377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58579331/20000000 : ℚ) : ℝ) ≤ Real.log ((350 : ℕ)) / 2 := by
    have h := (log_br_350).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((350 : ℕ)) / 2 ≤ ((14644833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_350).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3478649/10000000) (δ := 247/25000000) (ψ := -555759/1000000) 395 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t350 : ((47659852347/5000000000000 : ℚ) : ℝ) ≤ stT395o2 350 := by
  have hc : ((178327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((350 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47659852347/5000000000000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((178327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c351 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((351 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-93693/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29303931/10000000 : ℚ) : ℝ) ≤ Real.log ((351 : ℕ)) / 2 := by
    have h := (log_br_351).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((351 : ℕ)) / 2 ≤ ((58607863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_351).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4887367/10000000) (δ := 993/100000000) (ψ := -555759/1000000) 395 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t351 : ((-100032682771/5000000000000 : ℚ) : ℝ) ≤ stT395o2 351 := by
  have hc : ((-187411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((351 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100032682771/5000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-187411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c352 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((352 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-811093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58636311/20000000 : ℚ) : ℝ) ≤ Real.log ((352 : ℕ)) / 2 := by
    have h := (log_br_352).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((352 : ℕ)) / 2 ≤ ((7329539/2500000 : ℚ) : ℝ) := by
    have h := (log_br_352).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6292037/10000000) (δ := 10073/1000000000) (ψ := -555759/1000000) 395 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t352 : ((-216170420643/5000000000000 : ℚ) : ℝ) ≤ stT395o2 352 := by
  have hc : ((-811143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((352 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216170420643/5000000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-811143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c353 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((353 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-997921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1466617/500000 : ℚ) : ℝ) ≤ Real.log ((353 : ℕ)) / 2 := by
    have h := (log_br_353).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((353 : ℕ)) / 2 ≤ ((58664681/20000000 : ℚ) : ℝ) := by
    have h := (log_br_353).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1923189/2500000) (δ := 9923/1000000000) (ψ := -555759/1000000) 395 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t353 : ((-531167070837/10000000000000 : ℚ) : ℝ) ≤ stT395o2 353 := by
  have hc : ((-997971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((353 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-531167070837/10000000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-997971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c354 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((354 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-44017/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58692969/20000000 : ℚ) : ℝ) ≤ Real.log ((354 : ℕ)) / 2 := by
    have h := (log_br_354).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((354 : ℕ)) / 2 ≤ ((5869297/2000000 : ℚ) : ℝ) := by
    have h := (log_br_354).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3309219/5000000) (δ := 247/25000000) (ψ := -555759/1000000) 395 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t354 : ((-9358457661/200000000000 : ℚ) : ℝ) ≤ stT395o2 354 := by
  have hc : ((-88039/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((354 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9358457661/200000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-88039/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c355 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((355 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-496421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58721177/20000000 : ℚ) : ℝ) ≤ Real.log ((355 : ℕ)) / 2 := by
    have h := (log_br_355).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((355 : ℕ)) / 2 ≤ ((29360589/10000000 : ℚ) : ℝ) := by
    have h := (log_br_355).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1306417/2500000) (δ := 247/25000000) (ψ := -555759/1000000) 395 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t355 : ((-52699900179/2000000000000 : ℚ) : ℝ) ≤ stT395o2 355 := by
  have hc : ((-496471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((355 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52699900179/2000000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-496471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c356 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((356 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((36089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58749307/20000000 : ℚ) : ℝ) ≤ Real.log ((356 : ℕ)) / 2 := by
    have h := (log_br_356).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((356 : ℕ)) / 2 ≤ ((14687327/5000000 : ℚ) : ℝ) := by
    have h := (log_br_356).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3836749/10000000) (δ := 499/50000000) (ψ := -555759/1000000) 395 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t356 : ((9550298961/5000000000000 : ℚ) : ℝ) ≤ stT395o2 356 := by
  have hc : ((36039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((356 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9550298961/5000000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((36039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c357 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((357 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((556431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58777357/20000000 : ℚ) : ℝ) ≤ Real.log ((357 : ℕ)) / 2 := by
    have h := (log_br_357).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((357 : ℕ)) / 2 ≤ ((29388679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_357).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2451781/10000000) (δ := 10073/1000000000) (ψ := -555759/1000000) 395 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t357 : ((36808497817/1250000000000 : ℚ) : ℝ) ≤ stT395o2 357 := by
  have hc : ((556381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((357 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36808497817/1250000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((556381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c358 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((358 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((113711/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58805329/20000000 : ℚ) : ℝ) ≤ Real.log ((358 : ℕ)) / 2 := by
    have h := (log_br_358).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((358 : ℕ)) / 2 ≤ ((5880533/2000000 : ℚ) : ℝ) := by
    have h := (log_br_358).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1070663/10000000) (δ := 247/25000000) (ψ := -555759/1000000) 395 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t358 : ((60094779651/1250000000000 : ℚ) : ℝ) ≤ stT395o2 358 := by
  have hc : ((454819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((358 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60094779651/1250000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((454819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c359 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((359 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((992489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58833223/20000000 : ℚ) : ℝ) ≤ Real.log ((359 : ℕ)) / 2 := by
    have h := (log_br_359).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((359 : ℕ)) / 2 ≤ ((7354153/2500000 : ℚ) : ℝ) := by
    have h := (log_br_359).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 306603/10000000) (δ := 9973/1000000000) (ψ := -555759/1000000) 395 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t359 : ((523788462981/10000000000000 : ℚ) : ℝ) ≤ stT395o2 359 := by
  have hc : ((992439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((359 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((523788462981/10000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((992439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c360 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((360 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((782561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((735763/250000 : ℚ) : ℝ) ≤ Real.log ((360 : ℕ)) / 2 := by
    have h := (log_br_360).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((360 : ℕ)) / 2 ≤ ((58861041/20000000 : ℚ) : ℝ) := by
    have h := (log_br_360).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 420017/2500000) (δ := 1003/100000000) (ψ := -555759/1000000) 395 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t360 : ((206209646253/5000000000000 : ℚ) : ℝ) ≤ stT395o2 360 := by
  have hc : ((782511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((360 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206209646253/5000000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((782511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c361 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((361 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((171883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58888779/20000000 : ℚ) : ℝ) ≤ Real.log ((361 : ℕ)) / 2 := by
    have h := (log_br_361).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((361 : ℕ)) / 2 ≤ ((2944439/1000000 : ℚ) : ℝ) := by
    have h := (log_br_361).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3049681/10000000) (δ := 499/50000000) (ψ := -555759/1000000) 395 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t361 : ((9045144327/500000000000 : ℚ) : ℝ) ≤ stT395o2 361 := by
  have hc : ((85929/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((361 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9045144327/500000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((85929/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c362 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((362 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-194179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29458221/10000000 : ℚ) : ℝ) ≤ Real.log ((362 : ℕ)) / 2 := by
    have h := (log_br_362).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((362 : ℕ)) / 2 ≤ ((58916443/20000000 : ℚ) : ℝ) := by
    have h := (log_br_362).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4415541/10000000) (δ := 10023/1000000000) (ψ := -555759/1000000) 395 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t362 : ((-102084625881/10000000000000 : ℚ) : ℝ) ≤ stT395o2 362 := by
  have hc : ((-194229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((362 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102084625881/10000000000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-194229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c363 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((363 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-168617/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14736007/5000000 : ℚ) : ℝ) ≤ Real.log ((363 : ℕ)) / 2 := by
    have h := (log_br_363).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((363 : ℕ)) / 2 ≤ ((58944029/20000000 : ℚ) : ℝ) := by
    have h := (log_br_363).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3611/6250) (δ := 9923/1000000000) (ψ := -555759/1000000) 395 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t363 : ((-2765861059/78125000000 : ℚ) : ℝ) ≤ stT395o2 363 := by
  have hc : ((-337259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((363 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2765861059/78125000000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-337259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c364 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((364 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-119879/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29485769/10000000 : ℚ) : ℝ) ≤ Real.log ((364 : ℕ)) / 2 := by
    have h := (log_br_364).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((364 : ℕ)) / 2 ≤ ((58971539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_364).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3567953/5000000) (δ := 10023/1000000000) (ψ := -555759/1000000) 395 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t364 : ((-251348058363/5000000000000 : ℚ) : ℝ) ≤ stT395o2 364 := by
  have hc : ((-479541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((364 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251348058363/5000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-479541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c365 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((365 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-967761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58998973/20000000 : ℚ) : ℝ) ≤ Real.log ((365 : ℕ)) / 2 := by
    have h := (log_br_365).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((365 : ℕ)) / 2 ≤ ((29499487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_365).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3608727/5000000) (δ := 4983/500000000) (ψ := -555759/1000000) 395 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t365 : ((-15830484527/312500000000 : ℚ) : ℝ) ≤ stT395o2 365 := by
  have hc : ((-967811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((365 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15830484527/312500000000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-967811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c366 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((366 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-140061/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59026333/20000000 : ℚ) : ℝ) ≤ Real.log ((366 : ℕ)) / 2 := by
    have h := (log_br_366).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((366 : ℕ)) / 2 ≤ ((29513167/10000000 : ℚ) : ℝ) := by
    have h := (log_br_366).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2933277/5000000) (δ := 4983/500000000) (ψ := -555759/1000000) 395 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t366 : ((-73216372339/2000000000000 : ℚ) : ℝ) ≤ stT395o2 366 := by
  have hc : ((-140071/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((366 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73216372339/2000000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-140071/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c367 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((367 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-14671/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29526809/10000000 : ℚ) : ℝ) ≤ Real.log ((367 : ℕ)) / 2 := by
    have h := (log_br_367).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((367 : ℕ)) / 2 ≤ ((59053619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_367).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4519357/10000000) (δ := 2479/250000000) (ψ := -555759/1000000) 395 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t367 : ((-15319669107/1250000000000 : ℚ) : ℝ) ≤ stT395o2 367 := by
  have hc : ((-117393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((367 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15319669107/1250000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-117393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c368 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((368 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((29597/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59080829/20000000 : ℚ) : ℝ) ≤ Real.log ((368 : ℕ)) / 2 := by
    have h := (log_br_368).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((368 : ℕ)) / 2 ≤ ((5908083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_368).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1587907/5000000) (δ := 4983/500000000) (ψ := -555759/1000000) 395 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t368 : ((964118457/62500000000 : ℚ) : ℝ) ≤ stT395o2 368 := by
  have hc : ((3699/12500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((368 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((964118457/62500000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((3699/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c369 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((369 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((742253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29553983/10000000 : ℚ) : ℝ) ≤ Real.log ((369 : ℕ)) / 2 := by
    have h := (log_br_369).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((369 : ℕ)) / 2 ≤ ((59107967/20000000 : ℚ) : ℝ) := by
    have h := (log_br_369).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -458981/2500000) (δ := 10037/1000000000) (ψ := -555759/1000000) 395 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t369 : ((386375295537/10000000000000 : ℚ) : ℝ) ≤ stT395o2 369 := by
  have hc : ((742203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((369 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((386375295537/10000000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((742203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c370 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((370 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((196019/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5913503/2000000 : ℚ) : ℝ) ≤ Real.log ((370 : ℕ)) / 2 := by
    have h := (log_br_370).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((370 : ℕ)) / 2 ≤ ((59135031/20000000 : ℚ) : ℝ) := by
    have h := (log_br_370).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -499639/10000000) (δ := 10037/1000000000) (ψ := -555759/1000000) 395 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t370 : ((815201431/16000000000 : ℚ) : ℝ) ≤ stT395o2 370 := by
  have hc : ((196009/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((370 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((815201431/16000000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((196009/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c371 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((371 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((472501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2958101/1000000 : ℚ) : ℝ) ≤ Real.log ((371 : ℕ)) / 2 := by
    have h := (log_br_371).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((371 : ℕ)) / 2 ≤ ((59162021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_371).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 26031/312500) (δ := 9937/1000000000) (ψ := -555759/1000000) 395 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t371 : ((30662156853/625000000000 : ℚ) : ℝ) ≤ stT395o2 371 := by
  have hc : ((118119/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((371 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).1
  have hw2 : ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((259587/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30662156853/625000000000 : ℚ) : ℝ)
      = ((259587/5000000 : ℚ) : ℝ) * ((118119/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c372 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((372 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((162193/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29594469/10000000 : ℚ) : ℝ) ≤ Real.log ((372 : ℕ)) / 2 := by
    have h := (log_br_372).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((372 : ℕ)) / 2 ≤ ((59188939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_372).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 540517/2500000) (δ := 2479/250000000) (ψ := -555759/1000000) 395 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t372 : ((6726922779/200000000000 : ℚ) : ℝ) ≤ stT395o2 372 := by
  have hc : ((324361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((372 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6726922779/200000000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((324361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c373 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((373 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((174857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7401973/2500000 : ℚ) : ℝ) ≤ Real.log ((373 : ℕ)) / 2 := by
    have h := (log_br_373).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((373 : ℕ)) / 2 ≤ ((11843157/4000000 : ℚ) : ℝ) := by
    have h := (log_br_373).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3487589/10000000) (δ := 313/31250000) (ψ := -555759/1000000) 395 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t373 : ((4525578423/500000000000 : ℚ) : ℝ) ≤ stT395o2 373 := by
  have hc : ((174807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((373 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4525578423/500000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((174807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c374 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((374 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-8643/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59242557/20000000 : ℚ) : ℝ) ≤ Real.log ((374 : ℕ)) / 2 := by
    have h := (log_br_374).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((374 : ℕ)) / 2 ≤ ((29621279/10000000 : ℚ) : ℝ) := by
    have h := (log_br_374).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2404753/5000000) (δ := 4983/500000000) (ψ := -555759/1000000) 395 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t374 : ((-558729743/31250000000 : ℚ) : ℝ) ≤ stT395o2 374 := by
  have hc : ((-34577/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((374 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-558729743/31250000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-34577/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c375 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((375 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-192747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2963463/1000000 : ℚ) : ℝ) ≤ Real.log ((375 : ℕ)) / 2 := by
    have h := (log_br_375).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((375 : ℕ)) / 2 ≤ ((59269261/20000000 : ℚ) : ℝ) := by
    have h := (log_br_375).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6127967/10000000) (δ := 9937/1000000000) (ψ := -555759/1000000) 395 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t375 : ((-99540620281/2500000000000 : ℚ) : ℝ) ≤ stT395o2 375 := by
  have hc : ((-385519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((375 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99540620281/2500000000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-385519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c376 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((376 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-98651/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59295891/20000000 : ℚ) : ℝ) ≤ Real.log ((376 : ℕ)) / 2 := by
    have h := (log_br_376).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((376 : ℕ)) / 2 ≤ ((14823973/5000000 : ℚ) : ℝ) := by
    have h := (log_br_376).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 930359/1250000) (δ := 5033/500000000) (ψ := -555759/1000000) 395 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t376 : ((-1589937013/31250000000 : ℚ) : ℝ) ≤ stT395o2 376 := by
  have hc : ((-3083/3125 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((376 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1589937013/31250000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-3083/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c377 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((377 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-58491/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59322451/20000000 : ℚ) : ℝ) ≤ Real.log ((377 : ℕ)) / 2 := by
    have h := (log_br_377).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((377 : ℕ)) / 2 ≤ ((14830613/5000000 : ℚ) : ℝ) := by
    have h := (log_br_377).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6953691/10000000) (δ := 9959/1000000000) (ψ := -555759/1000000) 395 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t377 : ((-241008429731/5000000000000 : ℚ) : ℝ) ≤ stT395o2 377 := by
  have hc : ((-467953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((377 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).2
  have h0 : (0:ℝ) ≤ ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241008429731/5000000000000 : ℚ) : ℝ)
      = ((515027/10000000 : ℚ) : ℝ) * ((-467953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c378 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((378 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-634609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59348941/20000000 : ℚ) : ℝ) ≤ Real.log ((378 : ℕ)) / 2 := by
    have h := (log_br_378).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((378 : ℕ)) / 2 ≤ ((29674471/10000000 : ℚ) : ℝ) := by
    have h := (log_br_378).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5645747/10000000) (δ := 4947/500000000) (ψ := -555759/1000000) 395 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t378 : ((-65286736671/2000000000000 : ℚ) : ℝ) ≤ stT395o2 378 := by
  have hc : ((-634659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((378 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65286736671/2000000000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-634659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c379 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((379 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-164931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29687681/10000000 : ℚ) : ℝ) ≤ Real.log ((379 : ℕ)) / 2 := by
    have h := (log_br_379).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((379 : ℕ)) / 2 ≤ ((59375363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_379).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -434121/1000000) (δ := 1243/125000000) (ψ := -555759/1000000) 395 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t379 : ((-42372565173/5000000000000 : ℚ) : ℝ) ≤ stT395o2 379 := by
  have hc : ((-164981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((379 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42372565173/5000000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-164981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c380 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((380 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((86833/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3712607/1250000 : ℚ) : ℝ) ≤ Real.log ((380 : ℕ)) / 2 := by
    have h := (log_br_380).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((380 : ℕ)) / 2 ≤ ((59401713/20000000 : ℚ) : ℝ) := by
    have h := (log_br_380).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3040179/10000000) (δ := 9909/1000000000) (ψ := -555759/1000000) 395 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t380 : ((89075922949/5000000000000 : ℚ) : ℝ) ≤ stT395o2 380 := by
  have hc : ((173641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((380 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89075922949/5000000000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((173641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c381 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((381 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((766757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59427993/20000000 : ℚ) : ℝ) ≤ Real.log ((381 : ℕ)) / 2 := by
    have h := (log_br_381).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((381 : ℕ)) / 2 ≤ ((29713997/10000000 : ℚ) : ℝ) := by
    have h := (log_br_381).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -348511/2000000) (δ := 10059/1000000000) (ψ := -555759/1000000) 395 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t381 : ((78559099341/2000000000000 : ℚ) : ℝ) ≤ stT395o2 381 := by
  have hc : ((766707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((381 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78559099341/2000000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((766707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c382 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((382 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((491983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29727103/10000000 : ℚ) : ℝ) ≤ Real.log ((382 : ℕ)) / 2 := by
    have h := (log_br_382).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((382 : ℕ)) / 2 ≤ ((59454207/20000000 : ℚ) : ℝ) := by
    have h := (log_br_382).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -14009/312500) (δ := 10009/1000000000) (ψ := -555759/1000000) 395 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t382 : ((31463419869/625000000000 : ℚ) : ℝ) ≤ stT395o2 382 := by
  have hc : ((245979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((382 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31463419869/625000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((245979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c383 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((383 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((235937/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59480349/20000000 : ℚ) : ℝ) ≤ Real.log ((383 : ℕ)) / 2 := by
    have h := (log_br_383).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((383 : ℕ)) / 2 ≤ ((1189607/400000 : ℚ) : ℝ) := by
    have h := (log_br_383).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 842523/10000000) (δ := 4947/500000000) (ψ := -555759/1000000) 395 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t383 : ((235452651/4882812500 : ℚ) : ℝ) ≤ stT395o2 383 := by
  have hc : ((471849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((383 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235452651/4882812500 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((471849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c384 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((384 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((82309/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2380257/800000 : ℚ) : ℝ) ≤ Real.log ((384 : ℕ)) / 2 := by
    have h := (log_br_384).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((384 : ℕ)) / 2 ≤ ((29753213/10000000 : ℚ) : ℝ) := by
    have h := (log_br_384).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 85201/400000) (δ := 10059/1000000000) (ψ := -555759/1000000) 395 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t384 : ((16799966541/500000000000 : ℚ) : ℝ) ≤ stT395o2 384 := by
  have hc : ((329211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((384 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16799966541/500000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((329211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c385 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((385 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((203693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59532433/20000000 : ℚ) : ℝ) ≤ Real.log ((385 : ℕ)) / 2 := by
    have h := (log_br_385).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((385 : ℕ)) / 2 ≤ ((29766217/10000000 : ℚ) : ℝ) := by
    have h := (log_br_385).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 341417/1000000) (δ := 10059/1000000000) (ψ := -555759/1000000) 395 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t385 : ((103786044021/10000000000000 : ℚ) : ℝ) ≤ stT395o2 385 := by
  have hc : ((203643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((385 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103786044021/10000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((203643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c386 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((386 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-151189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59558373/20000000 : ℚ) : ℝ) ≤ Real.log ((386 : ℕ)) / 2 := by
    have h := (log_br_386).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((386 : ℕ)) / 2 ≤ ((29779187/10000000 : ℚ) : ℝ) := by
    have h := (log_br_386).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2347479/5000000) (δ := 4947/500000000) (ψ := -555759/1000000) 395 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t386 : ((-38482980109/2500000000000 : ℚ) : ℝ) ≤ stT395o2 386 := by
  have hc : ((-75607/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((386 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38482980109/2500000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-75607/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c387 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((387 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-364951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29792123/10000000 : ℚ) : ℝ) ≤ Real.log ((387 : ℕ)) / 2 := by
    have h := (log_br_387).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((387 : ℕ)) / 2 ≤ ((59584247/20000000 : ℚ) : ℝ) := by
    have h := (log_br_387).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5972437/10000000) (δ := 10009/1000000000) (ψ := -555759/1000000) 395 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t387 : ((-11595492819/312500000000 : ℚ) : ℝ) ≤ stT395o2 387 := by
  have hc : ((-22811/31250 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((387 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11595492819/312500000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-22811/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c388 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((388 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-970637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59610053/20000000 : ℚ) : ℝ) ≤ Real.log ((388 : ℕ)) / 2 := by
    have h := (log_br_388).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((388 : ℕ)) / 2 ≤ ((29805027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_388).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3623329/5000000) (δ := 4947/500000000) (ψ := -555759/1000000) 395 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t388 : ((-246396276019/5000000000000 : ℚ) : ℝ) ≤ stT395o2 388 := by
  have hc : ((-970687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((388 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246396276019/5000000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-970687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c389 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((389 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-482489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59635793/20000000 : ℚ) : ℝ) ≤ Real.log ((389 : ℕ)) / 2 := by
    have h := (log_br_389).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((389 : ℕ)) / 2 ≤ ((29817897/10000000 : ℚ) : ℝ) := by
    have h := (log_br_389).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7190393/10000000) (δ := 311/31250000) (ψ := -555759/1000000) 395 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t389 : ((-122322365397/2500000000000 : ℚ) : ℝ) ≤ stT395o2 389 := by
  have hc : ((-241257/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((389 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122322365397/2500000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-241257/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c390 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((390 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-71617/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59661467/20000000 : ℚ) : ℝ) ≤ Real.log ((390 : ℕ)) / 2 := by
    have h := (log_br_390).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((390 : ℕ)) / 2 ≤ ((14915367/5000000 : ℚ) : ℝ) := by
    have h := (log_br_390).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5922739/10000000) (δ := 9901/1000000000) (ψ := -555759/1000000) 395 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t390 : ((-1813361607/50000000000 : ℚ) : ℝ) ≤ stT395o2 390 := by
  have hc : ((-35811/50000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((390 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1813361607/50000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-35811/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c391 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((391 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-144193/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2387483/800000 : ℚ) : ℝ) ≤ Real.log ((391 : ℕ)) / 2 := by
    have h := (log_br_391).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((391 : ℕ)) / 2 ≤ ((14921769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_391).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -582293/1250000) (δ := 9901/1000000000) (ψ := -555759/1000000) 395 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t391 : ((-18233553849/1250000000000 : ℚ) : ℝ) ≤ stT395o2 391 := by
  have hc : ((-72109/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((391 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).2
  have h0 : (0:ℝ) ≤ ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18233553849/1250000000000 : ℚ) : ℝ)
      = ((252861/5000000 : ℚ) : ℝ) * ((-72109/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c392 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((392 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((4207/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29856309/10000000 : ℚ) : ℝ) ≤ Real.log ((392 : ℕ)) / 2 := by
    have h := (log_br_392).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((392 : ℕ)) / 2 ≤ ((59712619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_392).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1698579/5000000) (δ := 10051/1000000000) (ψ := -555759/1000000) 395 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t392 : ((265543707/25000000000 : ℚ) : ℝ) ≤ stT395o2 392 := by
  have hc : ((2103/10000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((392 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265543707/25000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((2103/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c393 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((393 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((655711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3733631/1250000 : ℚ) : ℝ) ≤ Real.log ((393 : ℕ)) / 2 := by
    have h := (log_br_393).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((393 : ℕ)) / 2 ≤ ((59738097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_393).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1069591/5000000) (δ := 9951/1000000000) (ψ := -555759/1000000) 395 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t393 : ((330737045213/10000000000000 : ℚ) : ℝ) ≤ stT395o2 393 := by
  have hc : ((655661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((393 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330737045213/10000000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((655661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c394 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((394 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((37523/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59763509/20000000 : ℚ) : ℝ) ≤ Real.log ((394 : ℕ)) / 2 := by
    have h := (log_br_394).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((394 : ℕ)) / 2 ≤ ((5976351/2000000 : ℚ) : ℝ) := by
    have h := (log_br_394).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -176883/2000000) (δ := 10001/1000000000) (ψ := -555759/1000000) 395 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t394 : ((1181423727/25000000000 : ℚ) : ℝ) ≤ stT395o2 394 := by
  have hc : ((37521/40000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((394 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1181423727/25000000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((37521/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c395 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((395 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((247309/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59788857/20000000 : ℚ) : ℝ) ≤ Real.log ((395 : ℕ)) / 2 := by
    have h := (log_br_395).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((395 : ℕ)) / 2 ≤ ((29894429/10000000 : ℚ) : ℝ) := by
    have h := (log_br_395).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 183571/5000000) (δ := 311/31250000) (ψ := -555759/1000000) 395 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t395 : ((124428223161/2500000000000 : ℚ) : ℝ) ≤ stT395o2 395 := by
  have hc : ((494593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((395 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124428223161/2500000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((494593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c396 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((396 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((199589/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29907071/10000000 : ℚ) : ℝ) ≤ Real.log ((396 : ℕ)) / 2 := by
    have h := (log_br_396).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((396 : ℕ)) / 2 ≤ ((59814143/20000000 : ℚ) : ℝ) := by
    have h := (log_br_396).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1615589/10000000) (δ := 4951/500000000) (ψ := -555759/1000000) 395 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t396 : ((100290783627/2500000000000 : ℚ) : ℝ) ≤ stT395o2 396 := by
  have hc : ((399153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((396 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100290783627/2500000000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((399153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c397 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((397 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((82731/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29919681/10000000 : ℚ) : ℝ) ≤ Real.log ((397 : ℕ)) / 2 := by
    have h := (log_br_397).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((397 : ℕ)) / 2 ≤ ((59839363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_397).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2860827/10000000) (δ := 10051/1000000000) (ψ := -555759/1000000) 395 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t397 : ((8303285817/400000000000 : ℚ) : ℝ) ≤ stT395o2 397 := by
  have hc : ((82721/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((397 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).1
  have hw2 : ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((100377/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8303285817/400000000000 : ℚ) : ℝ)
      = ((100377/2000000 : ℚ) : ℝ) * ((82721/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c398 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((398 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-70347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1496613/500000 : ℚ) : ℝ) ≤ Real.log ((398 : ℕ)) / 2 := by
    have h := (log_br_398).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((398 : ℕ)) / 2 ≤ ((59864521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_398).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4103003/10000000) (δ := 9951/1000000000) (ψ := -555759/1000000) 395 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t398 : ((-7057369647/2000000000000 : ℚ) : ℝ) ≤ stT395o2 398 := by
  have hc : ((-70397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((398 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7057369647/2000000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-70397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c399 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((399 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-53627/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29944807/10000000 : ℚ) : ℝ) ≤ Real.log ((399 : ℕ)) / 2 := by
    have h := (log_br_399).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((399 : ℕ)) / 2 ≤ ((11977923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_399).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5342019/10000000) (δ := 4951/500000000) (ψ := -555759/1000000) 395 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t399 : ((-209762713/7812500000 : ℚ) : ℝ) ≤ stT395o2 399 := by
  have hc : ((-1676/3125 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((399 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209762713/7812500000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-1676/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c400 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((400 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-436269/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11982929/4000000 : ℚ) : ℝ) ≤ Real.log ((400 : ℕ)) / 2 := by
    have h := (log_br_400).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((400 : ℕ)) / 2 ≤ ((29957323/10000000 : ℚ) : ℝ) := by
    have h := (log_br_400).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 263117/400000) (δ := 10001/1000000000) (ψ := -555759/1000000) 395 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t400 : ((-109073718147/2500000000000 : ℚ) : ℝ) ≤ stT395o2 400 := by
  have hc : ((-218147/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((400 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109073718147/2500000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-218147/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c401 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((401 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-999851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29969807/10000000 : ℚ) : ℝ) ≤ Real.log ((401 : ℕ)) / 2 := by
    have h := (log_br_401).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((401 : ℕ)) / 2 ≤ ((11987923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_401).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7810769/10000000) (δ := 4951/500000000) (ψ := -555759/1000000) 395 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t401 : ((-499327561677/10000000000000 : ℚ) : ℝ) ≤ stT395o2 401 := by
  have hc : ((-999901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((401 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-499327561677/10000000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-999901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c402 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((402 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-13898/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1499113/500000 : ℚ) : ℝ) ≤ Real.log ((402 : ℕ)) / 2 := by
    have h := (log_br_402).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((402 : ℕ)) / 2 ≤ ((59964521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_402).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -333373/500000) (δ := 5029/500000000) (ψ := -555759/1000000) 395 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t402 : ((-44365354511/1000000000000 : ℚ) : ℝ) ≤ stT395o2 402 := by
  have hc : ((-444761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((402 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44365354511/1000000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-444761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c403 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((403 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-569173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11997873/4000000 : ℚ) : ℝ) ≤ Real.log ((403 : ℕ)) / 2 := by
    have h := (log_br_403).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((403 : ℕ)) / 2 ≤ ((29994683/10000000 : ℚ) : ℝ) := by
    have h := (log_br_403).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5440739/10000000) (δ := 2009/200000000) (ψ := -555759/1000000) 395 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t403 : ((-35443808541/1250000000000 : ℚ) : ℝ) ≤ stT395o2 403 := by
  have hc : ((-569223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((403 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35443808541/1250000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-569223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c404 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((404 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-4631/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15003537/5000000 : ℚ) : ℝ) ≤ Real.log ((404 : ℕ)) / 2 := by
    have h := (log_br_404).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((404 : ℕ)) / 2 ≤ ((60014149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_404).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2108539/5000000) (δ := 1979/200000000) (ψ := -555759/1000000) 395 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t404 : ((-2305005527/400000000000 : ℚ) : ℝ) ≤ stT395o2 404 := by
  have hc : ((-4633/40000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((404 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2305005527/400000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-4633/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c405 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((405 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((363689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6003887/2000000 : ℚ) : ℝ) ≤ Real.log ((405 : ℕ)) / 2 := by
    have h := (log_br_405).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((405 : ℕ)) / 2 ≤ ((60038871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_405).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2996429/10000000) (δ := 4979/500000000) (ψ := -555759/1000000) 395 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t405 : ((180693310017/10000000000000 : ℚ) : ℝ) ≤ stT395o2 405 := by
  have hc : ((363639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((405 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180693310017/10000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((363639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c406 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((406 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((189343/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60063531/20000000 : ℚ) : ℝ) ≤ Real.log ((406 : ℕ)) / 2 := by
    have h := (log_br_406).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((406 : ℕ)) / 2 ≤ ((15015883/5000000 : ℚ) : ℝ) := by
    have h := (log_br_406).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -222349/1250000) (δ := 1251/125000000) (ψ := -555759/1000000) 395 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t406 : ((187926046351/5000000000000 : ℚ) : ℝ) ≤ stT395o2 406 := by
  have hc : ((378661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((406 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187926046351/5000000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((378661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c407 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((407 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((194929/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60088131/20000000 : ℚ) : ℝ) ≤ Real.log ((407 : ℕ)) / 2 := by
    have h := (log_br_407).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((407 : ℕ)) / 2 ≤ ((15022033/5000000 : ℚ) : ℝ) := by
    have h := (log_br_407).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -564167/10000000) (δ := 1251/125000000) (ψ := -555759/1000000) 395 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t407 : ((96617644839/2000000000000 : ℚ) : ℝ) ≤ stT395o2 407 := by
  have hc : ((194919/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((407 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96617644839/2000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((194919/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c408 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((408 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((966647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60112671/20000000 : ℚ) : ℝ) ≤ Real.log ((408 : ℕ)) / 2 := by
    have h := (log_br_408).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((408 : ℕ)) / 2 ≤ ((1878521/625000 : ℚ) : ℝ) := by
    have h := (log_br_408).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 129499/2000000) (δ := 1989/200000000) (ψ := -555759/1000000) 395 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t408 : ((478536076581/10000000000000 : ℚ) : ℝ) ≤ stT395o2 408 := by
  have hc : ((966597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((408 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((478536076581/10000000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((966597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c409 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((409 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((147359/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60137151/20000000 : ℚ) : ℝ) ≤ Real.log ((409 : ℕ)) / 2 := by
    have h := (log_br_409).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((409 : ℕ)) / 2 ≤ ((939643/312500 : ℚ) : ℝ) := by
    have h := (log_br_409).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 371239/2000000) (δ := 1989/200000000) (ψ := -555759/1000000) 395 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t409 : ((18214841333/500000000000 : ℚ) : ℝ) ≤ stT395o2 409 := by
  have hc : ((147349/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((409 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18214841333/500000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((147349/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c410 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((410 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((339159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60161571/20000000 : ℚ) : ℝ) ≤ Real.log ((410 : ℕ)) / 2 := by
    have h := (log_br_410).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((410 : ℕ)) / 2 ≤ ((15040393/5000000 : ℚ) : ℝ) := by
    have h := (log_br_410).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3061933/10000000) (δ := 1251/125000000) (ψ := -555759/1000000) 395 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t410 : ((20934215897/1250000000000 : ℚ) : ℝ) ≤ stT395o2 410 := by
  have hc : ((339109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((410 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20934215897/1250000000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((339109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c411 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((411 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-16837/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15046483/5000000 : ℚ) : ℝ) ≤ Real.log ((411 : ℕ)) / 2 := by
    have h := (log_br_411).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((411 : ℕ)) / 2 ≤ ((60185933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_411).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4264757/10000000) (δ := 1979/200000000) (ψ := -555759/1000000) 395 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t411 : ((-2077042217/312500000000 : ℚ) : ℝ) ≤ stT395o2 411 := by
  have hc : ((-67373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((411 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2077042217/312500000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-67373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c412 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((412 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-577/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60210233/20000000 : ℚ) : ℝ) ≤ Real.log ((412 : ℕ)) / 2 := by
    have h := (log_br_412).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((412 : ℕ)) / 2 ≤ ((30105117/10000000 : ℚ) : ℝ) := by
    have h := (log_br_412).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5464619/10000000) (δ := 2477/250000000) (ψ := -555759/1000000) 395 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t412 : ((-1137169353/40000000000 : ℚ) : ℝ) ≤ stT395o2 412 := by
  have hc : ((-11541/20000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((412 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1137169353/40000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-11541/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c413 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((413 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-111049/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2409379/800000 : ℚ) : ℝ) ≤ Real.log ((413 : ℕ)) / 2 := by
    have h := (log_br_413).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((413 : ℕ)) / 2 ≤ ((15058619/5000000 : ℚ) : ℝ) := by
    have h := (log_br_413).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 104087/156250) (δ := 1251/125000000) (ψ := -555759/1000000) 395 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t413 : ((-54646734757/1250000000000 : ℚ) : ℝ) ≤ stT395o2 413 := by
  have hc : ((-444221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((413 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54646734757/1250000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-444221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c414 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((414 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60258659/20000000 : ℚ) : ℝ) ≤ Real.log ((414 : ℕ)) / 2 := by
    have h := (log_br_414).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((414 : ℕ)) / 2 ≤ ((3012933/1000000 : ℚ) : ℝ) := by
    have h := (log_br_414).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7852311/10000000) (δ := 10037/1000000000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t414 : ((-4914985737/100000000000 : ℚ) : ℝ) ≤ stT395o2 414 := by
  have hc : ((-20001/20000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((414 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4914985737/100000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-20001/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c415 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((415 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-55519/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12056557/4000000 : ℚ) : ℝ) ≤ Real.log ((415 : ℕ)) / 2 := by
    have h := (log_br_415).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((415 : ℕ)) / 2 ≤ ((30141393/10000000 : ℚ) : ℝ) := by
    have h := (log_br_415).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6661089/10000000) (δ := 313/31250000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t415 : ((-218038049937/5000000000000 : ℚ) : ℝ) ≤ stT395o2 415 := by
  have hc : ((-444177/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((415 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218038049937/5000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-444177/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c416 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((416 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-36229/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15076713/5000000 : ℚ) : ℝ) ≤ Real.log ((416 : ℕ)) / 2 := by
    have h := (log_br_416).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((416 : ℕ)) / 2 ≤ ((60306853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_416).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5472781/10000000) (δ := 4983/500000000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t416 : ((-142114278387/5000000000000 : ℚ) : ℝ) ≤ stT395o2 416 := by
  have hc : ((-289857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((416 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142114278387/5000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-289857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c417 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((417 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-7181/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30165431/10000000 : ℚ) : ℝ) ≤ Real.log ((417 : ℕ)) / 2 := by
    have h := (log_br_417).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((417 : ℕ)) / 2 ≤ ((60330863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_417).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4287287/10000000) (δ := 5033/500000000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t417 : ((-7035563001/1000000000000 : ℚ) : ℝ) ≤ stT395o2 417 := by
  have hc : ((-14367/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((417 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7035563001/1000000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-14367/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c418 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((418 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((161517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30177407/10000000 : ℚ) : ℝ) ≤ Real.log ((418 : ℕ)) / 2 := by
    have h := (log_br_418).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((418 : ℕ)) / 2 ≤ ((12070963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_418).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3104657/10000000) (δ := 5033/500000000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t418 : ((3949407979/250000000000 : ℚ) : ℝ) ≤ stT395o2 418 := by
  have hc : ((40373/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((418 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3949407979/250000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((40373/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c419 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((419 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((143591/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60378709/20000000 : ℚ) : ℝ) ≤ Real.log ((419 : ℕ)) / 2 := by
    have h := (log_br_419).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((419 : ℕ)) / 2 ≤ ((6037871/2000000 : ℚ) : ℝ) := by
    have h := (log_br_419).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -962421/5000000) (δ := 9937/1000000000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t419 : ((70143769511/2000000000000 : ℚ) : ℝ) ≤ stT395o2 419 := by
  have hc : ((143581/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((419 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70143769511/2000000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((143581/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c420 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((420 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((955591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60402547/20000000 : ℚ) : ℝ) ≤ Real.log ((420 : ℕ)) / 2 := by
    have h := (log_br_420).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((420 : ℕ)) / 2 ≤ ((15100637/5000000 : ℚ) : ℝ) := by
    have h := (log_br_420).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -747841/10000000) (δ := 10037/1000000000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t420 : ((9325124619/200000000000 : ℚ) : ℝ) ≤ stT395o2 420 := by
  have hc : ((955541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((420 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9325124619/200000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((955541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c421 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((421 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((492747/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7553291/2500000 : ℚ) : ℝ) ≤ Real.log ((421 : ℕ)) / 2 := by
    have h := (log_br_421).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((421 : ℕ)) / 2 ≤ ((60426329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_421).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 213173/5000000) (δ := 9987/1000000000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t421 : ((12006896057/250000000000 : ℚ) : ℝ) ≤ stT395o2 421 := by
  have hc : ((246361/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((421 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12006896057/250000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((246361/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c422 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((422 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((802629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60450053/20000000 : ℚ) : ℝ) ≤ Real.log ((422 : ℕ)) / 2 := by
    have h := (log_br_422).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((422 : ℕ)) / 2 ≤ ((30225027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_422).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 199721/1250000) (δ := 9937/1000000000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t422 : ((48836129571/1250000000000 : ℚ) : ℝ) ≤ stT395o2 422 := by
  have hc : ((802579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((422 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48836129571/1250000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((802579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c423 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((423 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((447749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60473721/20000000 : ℚ) : ℝ) ≤ Real.log ((423 : ℕ)) / 2 := by
    have h := (log_br_423).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((423 : ℕ)) / 2 ≤ ((30236861/10000000 : ℚ) : ℝ) := by
    have h := (log_br_423).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 345797/1250000) (δ := 313/31250000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t423 : ((27209802123/1250000000000 : ℚ) : ℝ) ≤ stT395o2 423 := by
  have hc : ((447699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((423 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27209802123/1250000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((447699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c424 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((424 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-2111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30248667/10000000 : ℚ) : ℝ) ≤ Real.log ((424 : ℕ)) / 2 := by
    have h := (log_br_424).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((424 : ℕ)) / 2 ≤ ((12099467/4000000 : ℚ) : ℝ) := by
    have h := (log_br_424).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 983067/2500000) (δ := 5033/500000000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t424 : ((-1049474523/10000000000000 : ℚ) : ℝ) ≤ stT395o2 424 := by
  have hc : ((-2161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((424 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1049474523/10000000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-2161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c425 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((425 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-112633/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60520891/20000000 : ℚ) : ℝ) ≤ Real.log ((425 : ℕ)) / 2 := by
    have h := (log_br_425).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((425 : ℕ)) / 2 ≤ ((15130223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_425).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2547697/5000000) (δ := 10037/1000000000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t425 : ((-6830147247/312500000000 : ℚ) : ℝ) ≤ stT395o2 425 := by
  have hc : ((-225291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((425 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6830147247/312500000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-225291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c426 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((426 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-802531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60544393/20000000 : ℚ) : ℝ) ≤ Real.log ((426 : ℕ)) / 2 := by
    have h := (log_br_426).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((426 : ℕ)) / 2 ≤ ((30272197/10000000 : ℚ) : ℝ) := by
    have h := (log_br_426).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3127903/5000000) (δ := 313/31250000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t426 : ((-194426049831/5000000000000 : ℚ) : ℝ) ≤ stT395o2 426 := by
  have hc : ((-802581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((426 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194426049831/5000000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-802581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c427 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((427 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-492259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((378549/125000 : ℚ) : ℝ) ≤ Real.log ((427 : ℕ)) / 2 := by
    have h := (log_br_427).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((427 : ℕ)) / 2 ≤ ((60567841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_427).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7413501/10000000) (δ := 9987/1000000000) (ψ := -555759/1000000) 395 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t427 : ((-29779120657/625000000000 : ℚ) : ℝ) ≤ stT395o2 427 := by
  have hc : ((-123071/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((427 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29779120657/625000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-123071/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c428 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((428 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-479721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60591231/20000000 : ℚ) : ℝ) ≤ Real.log ((428 : ℕ)) / 2 := by
    have h := (log_br_428).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((428 : ℕ)) / 2 ≤ ((473369/156250 : ℚ) : ℝ) := by
    have h := (log_br_428).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7139531/10000000) (δ := 10023/1000000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t428 : ((-115947172137/2500000000000 : ℚ) : ℝ) ≤ stT395o2 428 := by
  have hc : ((-239873/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((428 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115947172137/2500000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-239873/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c429 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((429 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-733931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60614569/20000000 : ℚ) : ℝ) ≤ Real.log ((429 : ℕ)) / 2 := by
    have h := (log_br_429).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((429 : ℕ)) / 2 ≤ ((6061457/2000000 : ℚ) : ℝ) := by
    have h := (log_br_429).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2993609/5000000) (δ := 1003/100000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t429 : ((-70873939341/2000000000000 : ℚ) : ℝ) ≤ stT395o2 429 := by
  have hc : ((-733981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((429 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70873939341/2000000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-733981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c430 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((430 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-57/160 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15159463/5000000 : ℚ) : ℝ) ≤ Real.log ((430 : ℕ)) / 2 := by
    have h := (log_br_430).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((430 : ℕ)) / 2 ≤ ((60637853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_430).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4837619/10000000) (δ := 10073/1000000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t430 : ((-1718231809/100000000000 : ℚ) : ℝ) ≤ stT395o2 430 := by
  have hc : ((-3563/10000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((430 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1718231809/100000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-3563/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c431 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((431 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((94361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1516527/500000 : ℚ) : ℝ) ≤ Real.log ((431 : ℕ)) / 2 := by
    have h := (log_br_431).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((431 : ℕ)) / 2 ≤ ((60661081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_431).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3690737/10000000) (δ := 247/25000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t431 : ((45428005413/10000000000000 : ℚ) : ℝ) ≤ stT395o2 431 := by
  have hc : ((94311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((431 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45428005413/10000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((94311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c432 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((432 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((65571/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12136851/4000000 : ℚ) : ℝ) ≤ Real.log ((432 : ℕ)) / 2 := by
    have h := (log_br_432).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((432 : ℕ)) / 2 ≤ ((1896383/625000 : ℚ) : ℝ) := by
    have h := (log_br_432).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2546471/10000000) (δ := 10023/1000000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t432 : ((1009434891/40000000000 : ℚ) : ℝ) ≤ stT395o2 432 := by
  have hc : ((262259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((432 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1009434891/40000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((262259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c433 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((433 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((846229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60707377/20000000 : ℚ) : ℝ) ≤ Real.log ((433 : ℕ)) / 2 := by
    have h := (log_br_433).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((433 : ℕ)) / 2 ≤ ((30353689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_433).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1404823/10000000) (δ := 1003/100000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t433 : ((406647395851/10000000000000 : ℚ) : ℝ) ≤ stT395o2 433 := by
  have hc : ((846179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((433 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((406647395851/10000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((846179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c434 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((434 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((62147/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12146089/4000000 : ℚ) : ℝ) ≤ Real.log ((434 : ℕ)) / 2 := by
    have h := (log_br_434).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((434 : ℕ)) / 2 ≤ ((30365223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_434).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3323/125000) (δ := 9923/1000000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t434 : ((47727987453/1000000000000 : ℚ) : ℝ) ≤ stT395o2 434 := by
  have hc : ((497151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((434 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47727987453/1000000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((497151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c435 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((435 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((187997/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3037673/1000000 : ℚ) : ℝ) ≤ Real.log ((435 : ℕ)) / 2 := by
    have h := (log_br_435).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((435 : ℕ)) / 2 ≤ ((60753461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_435).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 435263/5000000) (δ := 10073/1000000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t435 : ((90132810981/2000000000000 : ℚ) : ℝ) ≤ stT395o2 435 := by
  have hc : ((187987/200000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((435 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90132810981/2000000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((187987/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c436 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((436 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((695479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30388211/10000000 : ℚ) : ℝ) ≤ Real.log ((436 : ℕ)) / 2 := by
    have h := (log_br_436).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((436 : ℕ)) / 2 ≤ ((60776423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_436).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1002137/5000000) (δ := 499/50000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t436 : ((333049988677/10000000000000 : ℚ) : ℝ) ≤ stT395o2 436 := by
  have hc : ((695429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((436 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((333049988677/10000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((695429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c437 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((437 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((31137/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60799331/20000000 : ℚ) : ℝ) ≤ Real.log ((437 : ℕ)) / 2 := by
    have h := (log_br_437).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((437 : ℕ)) / 2 ≤ ((15199833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_437).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1567703/5000000) (δ := 993/100000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t437 : ((930776753/62500000000 : ℚ) : ℝ) ≤ stT395o2 437 := by
  have hc : ((7783/25000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((437 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((930776753/62500000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((7783/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c438 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((438 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-33601/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60822189/20000000 : ℚ) : ℝ) ≤ Real.log ((438 : ℕ)) / 2 := by
    have h := (log_br_438).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((438 : ℕ)) / 2 ≤ ((6082219/2000000 : ℚ) : ℝ) := by
    have h := (log_br_438).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 213201/500000) (δ := 9923/1000000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t438 : ((-32122337913/5000000000000 : ℚ) : ℝ) ≤ stT395o2 438 := by
  have hc : ((-67227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((438 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32122337913/5000000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-67227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c439 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((439 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-4419/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30422497/10000000 : ℚ) : ℝ) ≤ Real.log ((439 : ℕ)) / 2 := by
    have h := (log_br_439).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((439 : ℕ)) / 2 ≤ ((12168999/4000000 : ℚ) : ℝ) := by
    have h := (log_br_439).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5390017/10000000) (δ := 9973/1000000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t439 : ((-5273161789/200000000000 : ℚ) : ℝ) ≤ stT395o2 439 := by
  have hc : ((-22097/40000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((439 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5273161789/200000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-22097/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c440 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((440 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-859649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60867747/20000000 : ℚ) : ℝ) ≤ Real.log ((440 : ℕ)) / 2 := by
    have h := (log_br_440).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((440 : ℕ)) / 2 ≤ ((15216937/5000000 : ℚ) : ℝ) := by
    have h := (log_br_440).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3256723/5000000) (δ := 993/100000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t440 : ((-102461505917/2500000000000 : ℚ) : ℝ) ≤ stT395o2 440 := by
  have hc : ((-859699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((440 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102461505917/2500000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-859699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c441 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((441 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-498071/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3805653/1250000 : ℚ) : ℝ) ≤ Real.log ((441 : ℕ)) / 2 := by
    have h := (log_br_441).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((441 : ℕ)) / 2 ≤ ((60890449/20000000 : ℚ) : ℝ) := by
    have h := (log_br_441).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1908577/2500000) (δ := 247/25000000) (ψ := -555759/1000000) 395 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t441 : ((-14824302021/312500000000 : ℚ) : ℝ) ≤ stT395o2 441 := by
  have hc : ((-31131/31250 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((441 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14824302021/312500000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-31131/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c442 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((442 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-234021/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30456549/10000000 : ℚ) : ℝ) ≤ Real.log ((442 : ℕ)) / 2 := by
    have h := (log_br_442).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((442 : ℕ)) / 2 ≤ ((60913099/20000000 : ℚ) : ℝ) := by
    have h := (log_br_442).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -434707/625000) (δ := 10073/1000000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t442 : ((-55659251171/1250000000000 : ℚ) : ℝ) ≤ stT395o2 442 := by
  have hc : ((-468067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((442 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55659251171/1250000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-468067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c443 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((443 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-86567/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60935697/20000000 : ℚ) : ℝ) ≤ Real.log ((443 : ℕ)) / 2 := by
    have h := (log_br_443).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((443 : ℕ)) / 2 ≤ ((30467849/10000000 : ℚ) : ℝ) := by
    have h := (log_br_443).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2919743/5000000) (δ := 9923/1000000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t443 : ((-32905799739/1000000000000 : ℚ) : ℝ) ≤ stT395o2 443 := by
  have hc : ((-346293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((443 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32905799739/1000000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-346293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c444 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((444 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-157129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12191649/4000000 : ℚ) : ℝ) ≤ Real.log ((444 : ℕ)) / 2 := by
    have h := (log_br_444).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((444 : ℕ)) / 2 ≤ ((30479123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_444).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2363089/5000000) (δ := 1003/100000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t444 : ((-37290994083/2500000000000 : ℚ) : ℝ) ≤ stT395o2 444 := by
  have hc : ((-78577/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((444 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37290994083/2500000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-78577/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c445 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((445 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((62159/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30490371/10000000 : ℚ) : ℝ) ≤ Real.log ((445 : ℕ)) / 2 := by
    have h := (log_br_445).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((445 : ℕ)) / 2 ≤ ((60980743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_445).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3615389/10000000) (δ := 247/25000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t445 : ((2945431203/500000000000 : ℚ) : ℝ) ≤ stT395o2 445 := by
  have hc : ((31067/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((445 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2945431203/500000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((31067/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c446 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((446 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((537921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61003189/20000000 : ℚ) : ℝ) ≤ Real.log ((446 : ℕ)) / 2 := by
    have h := (log_br_446).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((446 : ℕ)) / 2 ≤ ((6100319/2000000 : ℚ) : ℝ) := by
    have h := (log_br_446).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -626767/2500000) (δ := 1003/100000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t446 : ((254688910823/10000000000000 : ℚ) : ℝ) ≤ stT395o2 446 := by
  have hc : ((537871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((446 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254688910823/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((537871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c447 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((447 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((423493/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12205117/4000000 : ℚ) : ℝ) ≤ Real.log ((447 : ℕ)) / 2 := by
    have h := (log_br_447).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((447 : ℕ)) / 2 ≤ ((30512793/10000000 : ℚ) : ℝ) := by
    have h := (log_br_447).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -700633/5000000) (δ := 9923/1000000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t447 : ((50073291261/1250000000000 : ℚ) : ℝ) ≤ stT395o2 447 := by
  have hc : ((105867/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((447 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50073291261/1250000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((105867/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c448 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((448 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((99291/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15261983/5000000 : ℚ) : ℝ) ≤ Real.log ((448 : ℕ)) / 2 := by
    have h := (log_br_448).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((448 : ℕ)) / 2 ≤ ((61047933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_448).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -297883/10000000) (δ := 9973/1000000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t448 : ((4690816713/100000000000 : ℚ) : ℝ) ≤ stT395o2 448 := by
  have hc : ((49643/50000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((448 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4690816713/100000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((49643/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c449 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((449 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((47443/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15267557/5000000 : ℚ) : ℝ) ≤ Real.log ((449 : ℕ)) / 2 := by
    have h := (log_br_449).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((449 : ℕ)) / 2 ≤ ((61070229/20000000 : ℚ) : ℝ) := by
    have h := (log_br_449).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 401491/5000000) (δ := 9973/1000000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t449 : ((44777095449/1000000000000 : ℚ) : ℝ) ≤ stT395o2 449 := by
  have hc : ((94881/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((449 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44777095449/1000000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((94881/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c450 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((450 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((362221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2443699/800000 : ℚ) : ℝ) ≤ Real.log ((450 : ℕ)) / 2 := by
    have h := (log_br_450).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((450 : ℕ)) / 2 ≤ ((15273119/5000000 : ℚ) : ℝ) := by
    have h := (log_br_450).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 475357/2500000) (δ := 993/100000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t450 : ((10671290199/312500000000 : ℚ) : ℝ) ≤ stT395o2 450 := by
  have hc : ((90549/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((450 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10671290199/312500000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((90549/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c451 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((451 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((363307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61114673/20000000 : ℚ) : ℝ) ≤ Real.log ((451 : ℕ)) / 2 := by
    have h := (log_br_451).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((451 : ℕ)) / 2 ≤ ((30557337/10000000 : ℚ) : ℝ) := by
    have h := (log_br_451).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1498727/5000000) (δ := 9923/1000000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t451 : ((171050819417/10000000000000 : ℚ) : ℝ) ≤ stT395o2 451 := by
  have hc : ((363257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((451 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171050819417/10000000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((363257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c452 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((452 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-65561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61136821/20000000 : ℚ) : ℝ) ≤ Real.log ((452 : ℕ)) / 2 := by
    have h := (log_br_452).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((452 : ℕ)) / 2 ≤ ((30568411/10000000 : ℚ) : ℝ) := by
    have h := (log_br_452).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1022753/2500000) (δ := 1003/100000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t452 : ((-30860855571/10000000000000 : ℚ) : ℝ) ≤ stT395o2 452 := by
  have hc : ((-65611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((452 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30860855571/10000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-65611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c453 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((453 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-481253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61158921/20000000 : ℚ) : ℝ) ≤ Real.log ((453 : ℕ)) / 2 := by
    have h := (log_br_453).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((453 : ℕ)) / 2 ≤ ((30579461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_453).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5182199/10000000) (δ := 9923/1000000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t453 : ((-226135882823/10000000000000 : ℚ) : ℝ) ≤ stT395o2 453 := by
  have hc : ((-481303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((453 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-226135882823/10000000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-481303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c454 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((454 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-806123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61180971/20000000 : ℚ) : ℝ) ≤ Real.log ((454 : ℕ)) / 2 := by
    have h := (log_br_454).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((454 : ℕ)) / 2 ≤ ((15295243/5000000 : ℚ) : ℝ) := by
    have h := (log_br_454).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3135459/5000000) (δ := 993/100000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t454 : ((-94589084263/2500000000000 : ℚ) : ℝ) ≤ stT395o2 454 := by
  have hc : ((-806173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((454 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94589084263/2500000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-806173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c455 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((455 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-980331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30601487/10000000 : ℚ) : ℝ) ≤ Real.log ((455 : ℕ)) / 2 := by
    have h := (log_br_455).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((455 : ℕ)) / 2 ≤ ((2448119/800000 : ℚ) : ℝ) := by
    have h := (log_br_455).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1839329/2500000) (δ := 247/25000000) (ψ := -555759/1000000) 395 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t455 : ((-57451306981/1250000000000 : ℚ) : ℝ) ≤ stT395o2 455 := by
  have hc : ((-980381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((455 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57451306981/1250000000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-980381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c456 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((456 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-243133/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1913279/625000 : ℚ) : ℝ) ≤ Real.log ((456 : ℕ)) / 2 := by
    have h := (log_br_456).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((456 : ℕ)) / 2 ≤ ((61224929/20000000 : ℚ) : ℝ) := by
    have h := (log_br_456).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7266669/10000000) (δ := 5033/500000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t456 : ((-227726671263/5000000000000 : ℚ) : ℝ) ≤ stT395o2 456 := by
  have hc : ((-486291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((456 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227726671263/5000000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-486291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c457 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((457 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-785341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61246833/20000000 : ℚ) : ℝ) ≤ Real.log ((457 : ℕ)) / 2 := by
    have h := (log_br_457).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((457 : ℕ)) / 2 ≤ ((30623417/10000000 : ℚ) : ℝ) := by
    have h := (log_br_457).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6185109/10000000) (δ := 9937/1000000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t457 : ((-367390987371/10000000000000 : ℚ) : ℝ) ≤ stT395o2 457 := by
  have hc : ((-785391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((457 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-367390987371/10000000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-785391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c458 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((458 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-454269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61268691/20000000 : ℚ) : ℝ) ≤ Real.log ((458 : ℕ)) / 2 := by
    have h := (log_br_458).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((458 : ℕ)) / 2 ≤ ((15317173/5000000 : ℚ) : ℝ) := by
    have h := (log_br_458).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -510587/1000000) (δ := 10037/1000000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t458 : ((-21228963913/1000000000000 : ℚ) : ℝ) ≤ stT395o2 458 := by
  have hc : ((-454319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((458 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21228963913/1000000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-454319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c459 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((459 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-40773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30645251/10000000 : ℚ) : ℝ) ≤ Real.log ((459 : ℕ)) / 2 := by
    have h := (log_br_459).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((459 : ℕ)) / 2 ≤ ((61290503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_459).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -503619/1250000) (δ := 9987/1000000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t459 : ((-19054584303/10000000000000 : ℚ) : ℝ) ≤ stT395o2 459 := by
  have hc : ((-40823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((459 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19054584303/10000000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-40823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c460 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((460 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((379277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7664033/2500000 : ℚ) : ℝ) ≤ Real.log ((460 : ℕ)) / 2 := by
    have h := (log_br_460).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((460 : ℕ)) / 2 ≤ ((12262453/4000000 : ℚ) : ℝ) := by
    have h := (log_br_460).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1477227/5000000) (δ := 5033/500000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t460 : ((44203836801/2500000000000 : ℚ) : ℝ) ≤ stT395o2 460 := by
  have hc : ((379227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((460 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44203836801/2500000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((379227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c461 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((461 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((182429/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3066699/1000000 : ℚ) : ℝ) ≤ Real.log ((461 : ℕ)) / 2 := by
    have h := (log_br_461).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((461 : ℕ)) / 2 ≤ ((61333981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_461).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -941113/5000000) (δ := 9887/1000000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t461 : ((84959755209/2500000000000 : ℚ) : ℝ) ≤ stT395o2 461 := by
  have hc : ((364833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((461 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84959755209/2500000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((364833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c462 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((462 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((947667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((479341/156250 : ℚ) : ℝ) ≤ Real.log ((462 : ℕ)) / 2 := by
    have h := (log_br_462).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((462 : ℕ)) / 2 ≤ ((61355649/20000000 : ℚ) : ℝ) := by
    have h := (log_br_462).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -812369/10000000) (δ := 5033/500000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t462 : ((220435614157/5000000000000 : ℚ) : ℝ) ≤ stT395o2 462 := by
  have hc : ((947617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((462 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220435614157/5000000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((947617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c463 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((463 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((497397/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6137727/2000000 : ℚ) : ℝ) ≤ Real.log ((463 : ℕ)) / 2 := by
    have h := (log_br_463).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((463 : ℕ)) / 2 ≤ ((61377271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_463).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 127609/5000000) (δ := 9987/1000000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t463 : ((57787041477/1250000000000 : ℚ) : ℝ) ≤ stT395o2 463 := by
  have hc : ((124343/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((463 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57787041477/1250000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((124343/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c464 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((464 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((863719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12279769/4000000 : ℚ) : ℝ) ≤ Real.log ((464 : ℕ)) / 2 := by
    have h := (log_br_464).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((464 : ℕ)) / 2 ≤ ((30699423/10000000 : ℚ) : ℝ) := by
    have h := (log_br_464).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1320483/10000000) (δ := 313/31250000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t464 : ((200473984611/5000000000000 : ℚ) : ℝ) ≤ stT395o2 464 := by
  have hc : ((863669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((464 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200473984611/5000000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((863669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c465 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((465 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((578921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30710187/10000000 : ℚ) : ℝ) ≤ Real.log ((465 : ℕ)) / 2 := by
    have h := (log_br_465).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((465 : ℕ)) / 2 ≤ ((491363/160000 : ℚ) : ℝ) := by
    have h := (log_br_465).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1191739/5000000) (δ := 9987/1000000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t465 : ((134222239899/5000000000000 : ℚ) : ℝ) ≤ stT395o2 465 := by
  have hc : ((578871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((465 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134222239899/5000000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((578871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c466 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((466 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((191937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((960029/312500 : ℚ) : ℝ) ≤ Real.log ((466 : ℕ)) / 2 := by
    have h := (log_br_466).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((466 : ℕ)) / 2 ≤ ((61441857/20000000 : ℚ) : ℝ) := by
    have h := (log_br_466).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3444151/10000000) (δ := 5033/500000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t466 : ((88889925767/10000000000000 : ℚ) : ℝ) ≤ stT395o2 466 := by
  have hc : ((191887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((466 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88889925767/10000000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((191887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c467 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((467 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-228197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15365823/5000000 : ℚ) : ℝ) ≤ Real.log ((467 : ℕ)) / 2 := by
    have h := (log_br_467).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((467 : ℕ)) / 2 ≤ ((61463293/20000000 : ℚ) : ℝ) := by
    have h := (log_br_467).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2251277/5000000) (δ := 9887/1000000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t467 : ((-21124031603/2000000000000 : ℚ) : ℝ) ≤ stT395o2 467 := by
  have hc : ((-228247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((467 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21124031603/2000000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-228247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c468 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((468 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-151829/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30742341/10000000 : ℚ) : ℝ) ≤ Real.log ((468 : ℕ)) / 2 := by
    have h := (log_br_468).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((468 : ℕ)) / 2 ≤ ((61484683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_468).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1111737/2000000) (δ := 4983/500000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t468 : ((-140377770433/5000000000000 : ℚ) : ℝ) ≤ stT395o2 468 := by
  have hc : ((-303683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((468 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140377770433/5000000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-303683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c469 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((469 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-879229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61506027/20000000 : ℚ) : ℝ) ≤ Real.log ((469 : ℕ)) / 2 := by
    have h := (log_br_469).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((469 : ℕ)) / 2 ≤ ((15376507/5000000 : ℚ) : ℝ) := by
    have h := (log_br_469).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1322519/2000000) (δ := 10037/1000000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t469 : ((-203007056241/5000000000000 : ℚ) : ℝ) ≤ stT395o2 469 := by
  have hc : ((-879279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((469 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203007056241/5000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-879279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c470 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((470 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-997121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30763663/10000000 : ℚ) : ℝ) ≤ Real.log ((470 : ℕ)) / 2 := by
    have h := (log_br_470).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((470 : ℕ)) / 2 ≤ ((61527327/20000000 : ℚ) : ℝ) := by
    have h := (log_br_470).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7664233/10000000) (δ := 9987/1000000000) (ψ := -555759/1000000) 395 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t470 : ((-229980539243/5000000000000 : ℚ) : ℝ) ≤ stT395o2 470 := by
  have hc : ((-997171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((470 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229980539243/5000000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-997171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c471 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((471 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-470729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3077429/1000000 : ℚ) : ℝ) ≤ Real.log ((471 : ℕ)) / 2 := by
    have h := (log_br_471).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((471 : ℕ)) / 2 ≤ ((61548581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_471).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3497157/5000000) (δ := 4997/500000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t471 : ((-13557009069/312500000000 : ℚ) : ℝ) ≤ stT395o2 471 := by
  have hc : ((-235377/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((471 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13557009069/312500000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-235377/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c472 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((472 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-361471/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61569789/20000000 : ℚ) : ℝ) ≤ Real.log ((472 : ℕ)) / 2 := by
    have h := (log_br_472).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((472 : ℕ)) / 2 ≤ ((6156979/2000000 : ℚ) : ℝ) := by
    have h := (log_br_472).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -74339/125000) (δ := 9909/1000000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t472 : ((-40623113/1220703125 : ℚ) : ℝ) ≤ stT395o2 472 := by
  have hc : ((-45187/62500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((472 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40623113/1220703125 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-45187/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c473 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((473 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-190123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61590953/20000000 : ℚ) : ℝ) ≤ Real.log ((473 : ℕ)) / 2 := by
    have h := (log_br_473).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((473 : ℕ)) / 2 ≤ ((30795477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_473).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4902147/10000000) (δ := 2511/250000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t473 : ((-21857560137/1250000000000 : ℚ) : ℝ) ≤ stT395o2 473 := by
  have hc : ((-47537/125000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((473 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).2
  have h0 : (0:ℝ) ≤ ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21857560137/1250000000000 : ℚ) : ℝ)
      = ((459801/10000000 : ℚ) : ℝ) * ((-47537/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c474 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((474 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((13527/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61612073/20000000 : ℚ) : ℝ) ≤ Real.log ((474 : ℕ)) / 2 := by
    have h := (log_br_474).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((474 : ℕ)) / 2 ≤ ((30806037/10000000 : ℚ) : ℝ) := by
    have h := (log_br_474).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3859347/10000000) (δ := 2511/250000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t474 : ((620167113/500000000000 : ℚ) : ℝ) ≤ stT395o2 474 := by
  have hc : ((6751/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((474 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((620167113/500000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((6751/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c475 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((475 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((428913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15408287/5000000 : ℚ) : ℝ) ≤ Real.log ((475 : ℕ)) / 2 := by
    have h := (log_br_475).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((475 : ℕ)) / 2 ≤ ((61633149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_475).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2818769/10000000) (δ := 4997/500000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t475 : ((196775639153/10000000000000 : ℚ) : ℝ) ≤ stT395o2 475 := by
  have hc : ((428863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((475 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196775639153/10000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((428863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c476 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((476 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((756949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30827089/10000000 : ℚ) : ℝ) ≤ Real.log ((476 : ℕ)) / 2 := by
    have h := (log_br_476).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((476 : ℕ)) / 2 ≤ ((61654179/20000000 : ℚ) : ℝ) := by
    have h := (log_br_476).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1780413/10000000) (δ := 4947/500000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t476 : ((346923899751/10000000000000 : ℚ) : ℝ) ≤ stT395o2 476 := by
  have hc : ((756899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((476 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((346923899751/10000000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((756899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c477 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((477 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((59751/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15418791/5000000 : ℚ) : ℝ) ≤ Real.log ((477 : ℕ)) / 2 := by
    have h := (log_br_477).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((477 : ℕ)) / 2 ≤ ((12335033/4000000 : ℚ) : ℝ) := by
    have h := (log_br_477).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -744229/10000000) (δ := 4997/500000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t477 : ((54713280061/1250000000000 : ℚ) : ℝ) ≤ stT395o2 477 := by
  have hc : ((477983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((477 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54713280061/1250000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((477983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c478 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((478 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((993287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61696107/20000000 : ℚ) : ℝ) ≤ Real.log ((478 : ℕ)) / 2 := by
    have h := (log_br_478).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((478 : ℕ)) / 2 ≤ ((15424027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_478).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 289831/10000000) (δ := 10009/1000000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t478 : ((454295678193/10000000000000 : ℚ) : ℝ) ≤ stT395o2 478 := by
  have hc : ((993237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((478 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).1
  have hw2 : ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((457389/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454295678193/10000000000000 : ℚ) : ℝ)
      = ((457389/10000000 : ℚ) : ℝ) * ((993237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c479 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((479 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((21587/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12343401/4000000 : ℚ) : ℝ) ≤ Real.log ((479 : ℕ)) / 2 := by
    have h := (log_br_479).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((479 : ℕ)) / 2 ≤ ((30858503/10000000 : ℚ) : ℝ) := by
    have h := (log_br_479).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 132167/1000000) (δ := 9909/1000000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t479 : ((39451066473/1000000000000 : ℚ) : ℝ) ≤ stT395o2 479 := by
  have hc : ((86343/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((479 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).1
  have hw2 : ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((456911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39451066473/1000000000000 : ℚ) : ℝ)
      = ((456911/10000000 : ℚ) : ℝ) * ((86343/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c480 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((480 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((147331/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61737861/20000000 : ℚ) : ℝ) ≤ Real.log ((480 : ℕ)) / 2 := by
    have h := (log_br_480).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((480 : ℕ)) / 2 ≤ ((30868931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_480).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 470287/2000000) (δ := 9909/1000000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t480 : ((26896527819/1000000000000 : ℚ) : ℝ) ≤ stT395o2 480 := by
  have hc : ((294637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((480 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).1
  have hw2 : ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26896527819/1000000000000 : ℚ) : ℝ)
      = ((91287/2000000 : ℚ) : ℝ) * ((294637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c481 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((481 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((108727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3859917/1250000 : ℚ) : ℝ) ≤ Real.log ((481 : ℕ)) / 2 := by
    have h := (log_br_481).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((481 : ℕ)) / 2 ≤ ((61758673/20000000 : ℚ) : ℝ) := by
    have h := (log_br_481).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1689489/5000000) (δ := 9959/1000000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t481 : ((619547049/62500000000 : ℚ) : ℝ) ≤ stT395o2 481 := by
  have hc : ((54351/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((481 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).1
  have hw2 : ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11399/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((619547049/62500000000 : ℚ) : ℝ)
      = ((11399/250000 : ℚ) : ℝ) * ((54351/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c482 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((482 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-2966/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61779441/20000000 : ℚ) : ℝ) ≤ Real.log ((482 : ℕ)) / 2 := by
    have h := (log_br_482).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((482 : ℕ)) / 2 ≤ ((30889721/10000000 : ℚ) : ℝ) := by
    have h := (log_br_482).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 137639/312500) (δ := 2511/250000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t482 : ((-675666629/78125000000 : ℚ) : ℝ) ≤ stT395o2 482 := by
  have hc : ((-94937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((482 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-675666629/78125000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-94937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c483 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((483 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-564891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30900083/10000000 : ℚ) : ℝ) ≤ Real.log ((483 : ℕ)) / 2 := by
    have h := (log_br_483).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((483 : ℕ)) / 2 ≤ ((61800167/20000000 : ℚ) : ℝ) := by
    have h := (log_br_483).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 169617/312500) (δ := 10059/1000000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t483 : ((-32132149257/1250000000000 : ℚ) : ℝ) ≤ stT395o2 483 := by
  have hc : ((-564941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((483 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).2
  have h0 : (0:ℝ) ≤ ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32132149257/1250000000000 : ℚ) : ℝ)
      = ((56877/1250000 : ℚ) : ℝ) * ((-564941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c484 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((484 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-211547/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61820849/20000000 : ℚ) : ℝ) ≤ Real.log ((484 : ℕ)) / 2 := by
    have h := (log_br_484).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((484 : ℕ)) / 2 ≤ ((1236417/400000 : ℚ) : ℝ) := by
    have h := (log_br_484).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 806121/1250000) (δ := 2511/250000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t484 : ((-96163524487/2500000000000 : ℚ) : ℝ) ≤ stT395o2 484 := by
  have hc : ((-423119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((484 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).2
  have h0 : (0:ℝ) ≤ ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96163524487/2500000000000 : ℚ) : ℝ)
      = ((227273/5000000 : ℚ) : ℝ) * ((-423119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c485 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((485 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-494053/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3865093/1250000 : ℚ) : ℝ) ≤ Real.log ((485 : ℕ)) / 2 := by
    have h := (log_br_485).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((485 : ℕ)) / 2 ≤ ((61841489/20000000 : ℚ) : ℝ) := by
    have h := (log_br_485).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3734009/5000000) (δ := 9959/1000000000) (ψ := -555759/1000000) 395 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t485 : ((-112174728003/2500000000000 : ℚ) : ℝ) ≤ stT395o2 485 := by
  have hc : ((-247039/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((485 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).2
  have h0 : (0:ℝ) ≤ ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112174728003/2500000000000 : ℚ) : ℝ)
      = ((454077/10000000 : ℚ) : ℝ) * ((-247039/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c486 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((486 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-96831/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30931043/10000000 : ℚ) : ℝ) ≤ Real.log ((486 : ℕ)) / 2 := by
    have h := (log_br_486).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((486 : ℕ)) / 2 ≤ ((61862087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_486).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7222919/10000000) (δ := 9951/1000000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t486 : ((-1098144449/25000000000 : ℚ) : ℝ) ≤ stT395o2 486 := by
  have hc : ((-24209/25000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((486 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1098144449/25000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-24209/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c487 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((487 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-790981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61882641/20000000 : ℚ) : ℝ) ≤ Real.log ((487 : ℕ)) / 2 := by
    have h := (log_br_487).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((487 : ℕ)) / 2 ≤ ((30941321/10000000 : ℚ) : ℝ) := by
    have h := (log_br_487).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -388001/625000) (δ := 10001/1000000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t487 : ((-44806368933/1250000000000 : ℚ) : ℝ) ≤ stT395o2 487 := by
  have hc : ((-791031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((487 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44806368933/1250000000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-791031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c488 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((488 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-2429/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30951577/10000000 : ℚ) : ℝ) ≤ Real.log ((488 : ℕ)) / 2 := by
    have h := (log_br_488).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((488 : ℕ)) / 2 ≤ ((12380631/4000000 : ℚ) : ℝ) := by
    have h := (log_br_488).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2597593/5000000) (δ := 5001/500000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t488 : ((-4398681843/200000000000 : ℚ) : ℝ) ≤ stT395o2 488 := by
  have hc : ((-9717/20000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((488 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4398681843/200000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-9717/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c489 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((489 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-51407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7740453/2500000 : ℚ) : ℝ) ≤ Real.log ((489 : ℕ)) / 2 := by
    have h := (log_br_489).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((489 : ℕ)) / 2 ≤ ((495389/160000 : ℚ) : ℝ) := by
    have h := (log_br_489).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -26153/62500) (δ := 4951/500000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t489 : ((-363412083/78125000000 : ℚ) : ℝ) ≤ stT395o2 489 := by
  have hc : ((-6429/62500 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((489 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-363412083/78125000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-6429/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c490 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((490 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((36997/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61944053/20000000 : ℚ) : ℝ) ≤ Real.log ((490 : ℕ)) / 2 := by
    have h := (log_br_490).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((490 : ℕ)) / 2 ≤ ((30972027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_490).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1587899/5000000) (δ := 311/31250000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t490 : ((66842729139/5000000000000 : ℚ) : ℝ) ≤ stT395o2 490 := by
  have hc : ((147963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((490 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).1
  have hw2 : ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451753/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66842729139/5000000000000 : ℚ) : ℝ)
      = ((451753/10000000 : ℚ) : ℝ) * ((147963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c491 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((491 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((80827/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61964441/20000000 : ℚ) : ℝ) ≤ Real.log ((491 : ℕ)) / 2 := by
    have h := (log_br_491).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((491 : ℕ)) / 2 ≤ ((30982221/10000000 : ℚ) : ℝ) := by
    have h := (log_br_491).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2169141/10000000) (δ := 10001/1000000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t491 : ((145895354919/5000000000000 : ℚ) : ℝ) ≤ stT395o2 491 := by
  have hc : ((323283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((491 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).1
  have hw2 : ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451293/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145895354919/5000000000000 : ℚ) : ℝ)
      = ((451293/10000000 : ℚ) : ℝ) * ((323283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c492 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((492 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((223363/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61984787/20000000 : ℚ) : ℝ) ≤ Real.log ((492 : ℕ)) / 2 := by
    have h := (log_br_492).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((492 : ℕ)) / 2 ≤ ((15496197/5000000 : ℚ) : ℝ) := by
    have h := (log_br_492).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1164557/10000000) (δ := 9901/1000000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t492 : ((100693999317/2500000000000 : ℚ) : ℝ) ≤ stT395o2 492 := by
  have hc : ((446701/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((492 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100693999317/2500000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((446701/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c493 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((493 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((9979/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62005091/20000000 : ℚ) : ℝ) ≤ Real.log ((493 : ℕ)) / 2 := by
    have h := (log_br_493).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((493 : ℕ)) / 2 ≤ ((15501273/5000000 : ℚ) : ℝ) := by
    have h := (log_br_493).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -162047/10000000) (δ := 9901/1000000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t493 : ((8988173789/200000000000 : ℚ) : ℝ) ≤ stT395o2 493 := by
  have hc : ((19957/20000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((493 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8988173789/200000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((19957/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c494 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((494 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((23607/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12405071/4000000 : ℚ) : ℝ) ≤ Real.log ((494 : ℕ)) / 2 := by
    have h := (log_br_494).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((494 : ℕ)) / 2 ≤ ((15506339/5000000 : ℚ) : ℝ) := by
    have h := (log_br_494).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 104811/1250000) (δ := 9901/1000000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t494 : ((42482890583/1000000000000 : ℚ) : ℝ) ≤ stT395o2 494 := by
  have hc : ((94423/100000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((494 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42482890583/1000000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((94423/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c495 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((495 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((741979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62045577/20000000 : ℚ) : ℝ) ≤ Real.log ((495 : ℕ)) / 2 := by
    have h := (log_br_495).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((495 : ℕ)) / 2 ≤ ((31022789/10000000 : ℚ) : ℝ) := by
    have h := (log_br_495).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1836949/10000000) (δ := 10001/1000000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t495 : ((166735929957/5000000000000 : ℚ) : ℝ) ≤ stT395o2 495 := by
  have hc : ((741929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((495 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166735929957/5000000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((741929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c496 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((496 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((211803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62065759/20000000 : ℚ) : ℝ) ≤ Real.log ((496 : ℕ)) / 2 := by
    have h := (log_br_496).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((496 : ℕ)) / 2 ≤ ((387911/125000 : ℚ) : ℝ) := by
    have h := (log_br_496).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 708359/2500000) (δ := 2513/250000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t496 : ((47545537557/2500000000000 : ℚ) : ℝ) ≤ stT395o2 496 := by
  have hc : ((105889/250000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((496 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47545537557/2500000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((105889/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c497 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((497 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((39627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((620859/200000 : ℚ) : ℝ) ≤ Real.log ((497 : ℕ)) / 2 := by
    have h := (log_br_497).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((497 : ℕ)) / 2 ≤ ((62085901/20000000 : ℚ) : ℝ) := by
    have h := (log_br_497).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3827897/10000000) (δ := 10051/1000000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t497 : ((17752698697/10000000000000 : ℚ) : ℝ) ≤ stT395o2 497 := by
  have hc : ((39577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((497 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17752698697/10000000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((39577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c498 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((498 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-349781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((31053/10000 : ℚ) : ℝ) ≤ Real.log ((498 : ℕ)) / 2 := by
    have h := (log_br_498).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((498 : ℕ)) / 2 ≤ ((62106001/20000000 : ℚ) : ℝ) := by
    have h := (log_br_498).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 964067/2000000) (δ := 4951/500000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t498 : ((-156763119241/10000000000000 : ℚ) : ℝ) ≤ stT395o2 498 := by
  have hc : ((-349831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((498 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156763119241/10000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-349831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c499 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((499 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-171053/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3106303/1000000 : ℚ) : ℝ) ≤ Real.log ((499 : ℕ)) / 2 := by
    have h := (log_br_499).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((499 : ℕ)) / 2 ≤ ((62126061/20000000 : ℚ) : ℝ) := by
    have h := (log_br_499).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5810797/10000000) (δ := 10051/1000000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t499 : ((-76579523861/2500000000000 : ℚ) : ℝ) ≤ stT395o2 499 := by
  have hc : ((-342131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((499 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76579523861/2500000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-342131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_c500 :
    |Real.cos (((395 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((-912321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log ((500 : ℕ)) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((500 : ℕ)) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1359857/2000000) (δ := 4951/500000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st395o2_t500 : ((-204012542197/5000000000000 : ℚ) : ℝ) ≤ stT395o2 500 := by
  have hc : ((-912371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((395 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st395o2_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204012542197/5000000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-912371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st395o2_p1 : ((16989/20000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT395o2 (i+1) := by
  rw [Finset.sum_range_one]
  exact st395o2_t1

theorem st395o2_p2 : ((338305274337/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 1, stT395o2 (i+1)) + stT395o2 2 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 1
    simpa using h
  have hprev := st395o2_p1
  have hstep := st395o2_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p3 : ((1870837332003/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 2, stT395o2 (i+1)) + stT395o2 3 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 2
    simpa using h
  have hprev := st395o2_p2
  have hstep := st395o2_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p4 : ((6781266145431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 3, stT395o2 (i+1)) + stT395o2 4 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 3
    simpa using h
  have hprev := st395o2_p3
  have hstep := st395o2_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p5 : ((965633615739/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 4, stT395o2 (i+1)) + stT395o2 5 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 4
    simpa using h
  have hprev := st395o2_p4
  have hstep := st395o2_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p6 : ((1394710061069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 5, stT395o2 (i+1)) + stT395o2 6 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 5
    simpa using h
  have hprev := st395o2_p5
  have hstep := st395o2_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p7 : ((1289031186869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 6, stT395o2 (i+1)) + stT395o2 7 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 6
    simpa using h
  have hprev := st395o2_p6
  have hstep := st395o2_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p8 : ((-2085438026227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 7, stT395o2 (i+1)) + stT395o2 8 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 7
    simpa using h
  have hprev := st395o2_p7
  have hstep := st395o2_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p9 : ((-97644107621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 8, stT395o2 (i+1)) + stT395o2 9 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 8
    simpa using h
  have hprev := st395o2_p8
  have hstep := st395o2_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p10 : ((-328516902271/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 9, stT395o2 (i+1)) + stT395o2 10 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 9
    simpa using h
  have hprev := st395o2_p9
  have hstep := st395o2_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p11 : ((-3106856534771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 10, stT395o2 (i+1)) + stT395o2 11 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 10
    simpa using h
  have hprev := st395o2_p10
  have hstep := st395o2_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p12 : ((-5266342013113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 11, stT395o2 (i+1)) + stT395o2 12 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 11
    simpa using h
  have hprev := st395o2_p11
  have hstep := st395o2_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p13 : ((-5909461424993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 12, stT395o2 (i+1)) + stT395o2 13 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 12
    simpa using h
  have hprev := st395o2_p12
  have hstep := st395o2_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p14 : ((-133216809749/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 13, stT395o2 (i+1)) + stT395o2 14 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 13
    simpa using h
  have hprev := st395o2_p13
  have hstep := st395o2_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p15 : ((-2702108955853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 14, stT395o2 (i+1)) + stT395o2 15 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 14
    simpa using h
  have hprev := st395o2_p14
  have hstep := st395o2_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p16 : ((-2537651455853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 15, stT395o2 (i+1)) + stT395o2 16 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 15
    simpa using h
  have hprev := st395o2_p15
  have hstep := st395o2_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p17 : ((-1052867915501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 16, stT395o2 (i+1)) + stT395o2 17 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 16
    simpa using h
  have hprev := st395o2_p16
  have hstep := st395o2_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p18 : ((1148189938759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 17, stT395o2 (i+1)) + stT395o2 18 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 17
    simpa using h
  have hprev := st395o2_p17
  have hstep := st395o2_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p19 : ((-299795412837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 18, stT395o2 (i+1)) + stT395o2 19 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 18
    simpa using h
  have hprev := st395o2_p18
  have hstep := st395o2_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p20 : ((-70115750637/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 19, stT395o2 (i+1)) + stT395o2 20 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 19
    simpa using h
  have hprev := st395o2_p19
  have hstep := st395o2_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p21 : ((155186824053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 20, stT395o2 (i+1)) + stT395o2 21 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 20
    simpa using h
  have hprev := st395o2_p20
  have hstep := st395o2_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p22 : ((161749141599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 21, stT395o2 (i+1)) + stT395o2 22 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 21
    simpa using h
  have hprev := st395o2_p21
  have hstep := st395o2_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p23 : ((-1098057934791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 22, stT395o2 (i+1)) + stT395o2 23 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 22
    simpa using h
  have hprev := st395o2_p22
  have hstep := st395o2_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p24 : ((186691718617/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 23, stT395o2 (i+1)) + stT395o2 24 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 23
    simpa using h
  have hprev := st395o2_p23
  have hstep := st395o2_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p25 : ((711362482037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 24, stT395o2 (i+1)) + stT395o2 25 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 24
    simpa using h
  have hprev := st395o2_p24
  have hstep := st395o2_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p26 : ((-1249885809091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 25, stT395o2 (i+1)) + stT395o2 26 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 25
    simpa using h
  have hprev := st395o2_p25
  have hstep := st395o2_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p27 : ((-996994173619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 26, stT395o2 (i+1)) + stT395o2 27 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 26
    simpa using h
  have hprev := st395o2_p26
  have hstep := st395o2_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p28 : ((-2117023859/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 27, stT395o2 (i+1)) + stT395o2 28 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 27
    simpa using h
  have hprev := st395o2_p27
  have hstep := st395o2_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p29 : ((305415969821/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 28, stT395o2 (i+1)) + stT395o2 29 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 28
    simpa using h
  have hprev := st395o2_p28
  have hstep := st395o2_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p30 : ((97456564007/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 29, stT395o2 (i+1)) + stT395o2 30 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 29
    simpa using h
  have hprev := st395o2_p29
  have hstep := st395o2_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p31 : ((4201984488659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 30, stT395o2 (i+1)) + stT395o2 31 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 30
    simpa using h
  have hprev := st395o2_p30
  have hstep := st395o2_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p32 : ((5943755489629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 31, stT395o2 (i+1)) + stT395o2 32 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 31
    simpa using h
  have hprev := st395o2_p31
  have hstep := st395o2_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p33 : ((7683415652213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 32, stT395o2 (i+1)) + stT395o2 33 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 32
    simpa using h
  have hprev := st395o2_p32
  have hstep := st395o2_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p34 : ((4624071120719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 33, stT395o2 (i+1)) + stT395o2 34 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 33
    simpa using h
  have hprev := st395o2_p33
  have hstep := st395o2_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p35 : ((5094970645823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 34, stT395o2 (i+1)) + stT395o2 35 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 34
    simpa using h
  have hprev := st395o2_p34
  have hstep := st395o2_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p36 : ((9976459582283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 35, stT395o2 (i+1)) + stT395o2 36 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 35
    simpa using h
  have hprev := st395o2_p35
  have hstep := st395o2_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p37 : ((8592764162973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 36, stT395o2 (i+1)) + stT395o2 37 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 36
    simpa using h
  have hprev := st395o2_p36
  have hstep := st395o2_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p38 : ((7128938991143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 37, stT395o2 (i+1)) + stT395o2 38 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 37
    simpa using h
  have hprev := st395o2_p37
  have hstep := st395o2_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p39 : ((7173563490051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 38, stT395o2 (i+1)) + stT395o2 39 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 38
    simpa using h
  have hprev := st395o2_p38
  have hstep := st395o2_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p40 : ((8701499358627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 39, stT395o2 (i+1)) + stT395o2 40 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 39
    simpa using h
  have hprev := st395o2_p39
  have hstep := st395o2_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p41 : ((9344438370261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 40, stT395o2 (i+1)) + stT395o2 41 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 40
    simpa using h
  have hprev := st395o2_p40
  have hstep := st395o2_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p42 : ((7969510209391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 41, stT395o2 (i+1)) + stT395o2 42 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 41
    simpa using h
  have hprev := st395o2_p41
  have hstep := st395o2_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p43 : ((7366983665833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 42, stT395o2 (i+1)) + stT395o2 43 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 42
    simpa using h
  have hprev := st395o2_p42
  have hstep := st395o2_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p44 : ((8833321577237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 43, stT395o2 (i+1)) + stT395o2 44 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 43
    simpa using h
  have hprev := st395o2_p43
  have hstep := st395o2_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p45 : ((8773861547693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 44, stT395o2 (i+1)) + stT395o2 45 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 44
    simpa using h
  have hprev := st395o2_p44
  have hstep := st395o2_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p46 : ((7422393431493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 45, stT395o2 (i+1)) + stT395o2 46 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 45
    simpa using h
  have hprev := st395o2_p45
  have hstep := st395o2_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p47 : ((4271554962209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 46, stT395o2 (i+1)) + stT395o2 47 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 46
    simpa using h
  have hprev := st395o2_p46
  have hstep := st395o2_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p48 : ((8744672913043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 47, stT395o2 (i+1)) + stT395o2 48 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 47
    simpa using h
  have hprev := st395o2_p47
  have hstep := st395o2_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p49 : ((7490872411523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 48, stT395o2 (i+1)) + stT395o2 49 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 48
    simpa using h
  have hprev := st395o2_p48
  have hstep := st395o2_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p50 : ((8819992215313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 49, stT395o2 (i+1)) + stT395o2 50 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 49
    simpa using h
  have hprev := st395o2_p49
  have hstep := st395o2_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p51 : ((8207248853647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 50, stT395o2 (i+1)) + stT395o2 51 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 50
    simpa using h
  have hprev := st395o2_p50
  have hstep := st395o2_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p52 : ((7876702885287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 51, stT395o2 (i+1)) + stT395o2 52 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 51
    simpa using h
  have hprev := st395o2_p51
  have hstep := st395o2_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p53 : ((8918552058477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 52, stT395o2 (i+1)) + stT395o2 53 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 52
    simpa using h
  have hprev := st395o2_p52
  have hstep := st395o2_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p54 : ((7574961666753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 53, stT395o2 (i+1)) + stT395o2 54 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 53
    simpa using h
  have hprev := st395o2_p53
  have hstep := st395o2_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p55 : ((8853688890423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 54, stT395o2 (i+1)) + stT395o2 55 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 54
    simpa using h
  have hprev := st395o2_p54
  have hstep := st395o2_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p56 : ((3933296158599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 55, stT395o2 (i+1)) + stT395o2 56 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 55
    simpa using h
  have hprev := st395o2_p55
  have hstep := st395o2_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p57 : ((847458032037/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 56, stT395o2 (i+1)) + stT395o2 57 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 56
    simpa using h
  have hprev := st395o2_p56
  have hstep := st395o2_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p58 : ((1646941658621/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 57, stT395o2 (i+1)) + stT395o2 58 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 57
    simpa using h
  have hprev := st395o2_p57
  have hstep := st395o2_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p59 : ((1633683731617/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 58, stT395o2 (i+1)) + stT395o2 59 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 58
    simpa using h
  have hprev := st395o2_p58
  have hstep := st395o2_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p60 : ((8461036649119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 59, stT395o2 (i+1)) + stT395o2 60 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 59
    simpa using h
  have hprev := st395o2_p59
  have hstep := st395o2_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p61 : ((400998052597/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 60, stT395o2 (i+1)) + stT395o2 61 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 60
    simpa using h
  have hprev := st395o2_p60
  have hstep := st395o2_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p62 : ((8539491791019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 61, stT395o2 (i+1)) + stT395o2 62 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 61
    simpa using h
  have hprev := st395o2_p61
  have hstep := st395o2_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p63 : ((1600562207261/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 62, stT395o2 (i+1)) + stT395o2 63 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 62
    simpa using h
  have hprev := st395o2_p62
  have hstep := st395o2_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p64 : ((1699899957261/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 63, stT395o2 (i+1)) + stT395o2 64 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 63
    simpa using h
  have hprev := st395o2_p63
  have hstep := st395o2_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p65 : ((8098486595469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 64, stT395o2 (i+1)) + stT395o2 65 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 64
    simpa using h
  have hprev := st395o2_p64
  have hstep := st395o2_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p66 : ((8346476377221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 65, stT395o2 (i+1)) + stT395o2 66 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 65
    simpa using h
  have hprev := st395o2_p65
  have hstep := st395o2_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p67 : ((4154091173723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 66, stT395o2 (i+1)) + stT395o2 67 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 66
    simpa using h
  have hprev := st395o2_p66
  have hstep := st395o2_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p68 : ((2021469114631/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 67, stT395o2 (i+1)) + stT395o2 68 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 67
    simpa using h
  have hprev := st395o2_p67
  have hstep := st395o2_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p69 : ((2150364986833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 68, stT395o2 (i+1)) + stT395o2 69 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 68
    simpa using h
  have hprev := st395o2_p68
  have hstep := st395o2_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p70 : ((974162335951/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 69, stT395o2 (i+1)) + stT395o2 70 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 69
    simpa using h
  have hprev := st395o2_p69
  have hstep := st395o2_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p71 : ((8841379405357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 70, stT395o2 (i+1)) + stT395o2 71 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 70
    simpa using h
  have hprev := st395o2_p70
  have hstep := st395o2_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p72 : ((1533957996969/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 71, stT395o2 (i+1)) + stT395o2 72 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 71
    simpa using h
  have hprev := st395o2_p71
  have hstep := st395o2_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p73 : ((878488150893/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 72, stT395o2 (i+1)) + stT395o2 73 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 72
    simpa using h
  have hprev := st395o2_p72
  have hstep := st395o2_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p74 : ((1986156714663/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 73, stT395o2 (i+1)) + stT395o2 74 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 73
    simpa using h
  have hprev := st395o2_p73
  have hstep := st395o2_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p75 : ((1038099677319/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 74, stT395o2 (i+1)) + stT395o2 75 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 74
    simpa using h
  have hprev := st395o2_p74
  have hstep := st395o2_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p76 : ((4271033530809/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 75, stT395o2 (i+1)) + stT395o2 76 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 75
    simpa using h
  have hprev := st395o2_p75
  have hstep := st395o2_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p77 : ((3875059192413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 76, stT395o2 (i+1)) + stT395o2 77 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 76
    simpa using h
  have hprev := st395o2_p76
  have hstep := st395o2_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p78 : ((177152242117/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 77, stT395o2 (i+1)) + stT395o2 78 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 77
    simpa using h
  have hprev := st395o2_p77
  have hstep := st395o2_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p79 : ((3914273495693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 78, stT395o2 (i+1)) + stT395o2 79 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 78
    simpa using h
  have hprev := st395o2_p78
  have hstep := st395o2_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p80 : ((8361800656967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 79, stT395o2 (i+1)) + stT395o2 80 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 79
    simpa using h
  have hprev := st395o2_p79
  have hstep := st395o2_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p81 : ((33486612727/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 80, stT395o2 (i+1)) + stT395o2 81 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 80
    simpa using h
  have hprev := st395o2_p80
  have hstep := st395o2_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p82 : ((1925308049/2500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 81, stT395o2 (i+1)) + stT395o2 82 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 81
    simpa using h
  have hprev := st395o2_p81
  have hstep := st395o2_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p83 : ((4397382860997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 82, stT395o2 (i+1)) + stT395o2 83 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 82
    simpa using h
  have hprev := st395o2_p82
  have hstep := st395o2_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p84 : ((2021181180081/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 83, stT395o2 (i+1)) + stT395o2 84 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 83
    simpa using h
  have hprev := st395o2_p83
  have hstep := st395o2_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p85 : ((7980957052467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 84, stT395o2 (i+1)) + stT395o2 85 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 84
    simpa using h
  have hprev := st395o2_p84
  have hstep := st395o2_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p86 : ((8843631592391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 85, stT395o2 (i+1)) + stT395o2 86 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 85
    simpa using h
  have hprev := st395o2_p85
  have hstep := st395o2_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p87 : ((7796130018419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 86, stT395o2 (i+1)) + stT395o2 87 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 86
    simpa using h
  have hprev := st395o2_p86
  have hstep := st395o2_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p88 : ((4140118579409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 87, stT395o2 (i+1)) + stT395o2 88 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 87
    simpa using h
  have hprev := st395o2_p87
  have hstep := st395o2_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p89 : ((8730226025261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 88, stT395o2 (i+1)) + stT395o2 89 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 88
    simpa using h
  have hprev := st395o2_p88
  have hstep := st395o2_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p90 : ((1924140073377/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 89, stT395o2 (i+1)) + stT395o2 90 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 89
    simpa using h
  have hprev := st395o2_p89
  have hstep := st395o2_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p91 : ((211375971093/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 90, stT395o2 (i+1)) + stT395o2 91 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 90
    simpa using h
  have hprev := st395o2_p90
  have hstep := st395o2_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p92 : ((1079449454121/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 91, stT395o2 (i+1)) + stT395o2 92 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 91
    simpa using h
  have hprev := st395o2_p91
  have hstep := st395o2_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p93 : ((959569248067/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 92, stT395o2 (i+1)) + stT395o2 93 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 92
    simpa using h
  have hprev := st395o2_p92
  have hstep := st395o2_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p94 : ((8504400327503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 93, stT395o2 (i+1)) + stT395o2 94 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 93
    simpa using h
  have hprev := st395o2_p93
  have hstep := st395o2_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p95 : ((8627027270019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 94, stT395o2 (i+1)) + stT395o2 95 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 94
    simpa using h
  have hprev := st395o2_p94
  have hstep := st395o2_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p96 : ((7678190627433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 95, stT395o2 (i+1)) + stT395o2 96 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 95
    simpa using h
  have hprev := st395o2_p95
  have hstep := st395o2_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p97 : ((8443145196411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 96, stT395o2 (i+1)) + stT395o2 97 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 96
    simpa using h
  have hprev := st395o2_p96
  have hstep := st395o2_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p98 : ((8705371564243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 97, stT395o2 (i+1)) + stT395o2 98 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 97
    simpa using h
  have hprev := st395o2_p97
  have hstep := st395o2_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p99 : ((7715053350791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 98, stT395o2 (i+1)) + stT395o2 99 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 98
    simpa using h
  have hprev := st395o2_p98
  have hstep := st395o2_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p100 : ((8267860797983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 99, stT395o2 (i+1)) + stT395o2 100 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 99
    simpa using h
  have hprev := st395o2_p99
  have hstep := st395o2_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p101 : ((8821905359879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 100, stT395o2 (i+1)) + stT395o2 101 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 100
    simpa using h
  have hprev := st395o2_p100
  have hstep := st395o2_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p102 : ((7854623837791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 101, stT395o2 (i+1)) + stT395o2 102 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 101
    simpa using h
  have hprev := st395o2_p101
  have hstep := st395o2_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p103 : ((1598505308663/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 102, stT395o2 (i+1)) + stT395o2 103 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 102
    simpa using h
  have hprev := st395o2_p102
  have hstep := st395o2_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p104 : ((1772639450687/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 103, stT395o2 (i+1)) + stT395o2 104 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 103
    simpa using h
  have hprev := st395o2_p103
  have hstep := st395o2_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p105 : ((8165070858669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 104, stT395o2 (i+1)) + stT395o2 105 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 104
    simpa using h
  have hprev := st395o2_p104
  have hstep := st395o2_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p106 : ((1544600143983/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 105, stT395o2 (i+1)) + stT395o2 106 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 105
    simpa using h
  have hprev := st395o2_p105
  have hstep := st395o2_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p107 : ((8672512384603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 106, stT395o2 (i+1)) + stT395o2 107 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 106
    simpa using h
  have hprev := st395o2_p106
  have hstep := st395o2_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p108 : ((8597826310987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 107, stT395o2 (i+1)) + stT395o2 108 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 107
    simpa using h
  have hprev := st395o2_p107
  have hstep := st395o2_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p109 : ((7690744985447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 108, stT395o2 (i+1)) + stT395o2 109 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 108
    simpa using h
  have hprev := st395o2_p108
  have hstep := st395o2_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p110 : ((8197162024817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 109, stT395o2 (i+1)) + stT395o2 110 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 109
    simpa using h
  have hprev := st395o2_p109
  have hstep := st395o2_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p111 : ((8874176729777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 110, stT395o2 (i+1)) + stT395o2 111 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 110
    simpa using h
  have hprev := st395o2_p110
  have hstep := st395o2_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p112 : ((1618186700701/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 111, stT395o2 (i+1)) + stT395o2 112 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 111
    simpa using h
  have hprev := st395o2_p111
  have hstep := st395o2_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p113 : ((1929201955271/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 112, stT395o2 (i+1)) + stT395o2 113 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 112
    simpa using h
  have hprev := st395o2_p112
  have hstep := st395o2_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p114 : ((8626577455949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 113, stT395o2 (i+1)) + stT395o2 114 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 113
    simpa using h
  have hprev := st395o2_p113
  have hstep := st395o2_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p115 : ((348248308101/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 114, stT395o2 (i+1)) + stT395o2 115 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 114
    simpa using h
  have hprev := st395o2_p114
  have hstep := st395o2_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p116 : ((1944754625031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 115, stT395o2 (i+1)) + stT395o2 116 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 115
    simpa using h
  have hprev := st395o2_p115
  have hstep := st395o2_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p117 : ((1985692409531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 116, stT395o2 (i+1)) + stT395o2 117 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 116
    simpa using h
  have hprev := st395o2_p116
  have hstep := st395o2_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p118 : ((2206333744703/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 117, stT395o2 (i+1)) + stT395o2 118 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 117
    simpa using h
  have hprev := st395o2_p117
  have hstep := st395o2_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p119 : ((8481823112639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 118, stT395o2 (i+1)) + stT395o2 119 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 118
    simpa using h
  have hprev := st395o2_p118
  have hstep := st395o2_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p120 : ((3833119756861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 119, stT395o2 (i+1)) + stT395o2 120 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 119
    simpa using h
  have hprev := st395o2_p119
  have hstep := st395o2_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p121 : ((2032266353633/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 120, stT395o2 (i+1)) + stT395o2 121 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 120
    simpa using h
  have hprev := st395o2_p120
  have hstep := st395o2_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p122 : ((8881854368963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 121, stT395o2 (i+1)) + stT395o2 122 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 121
    simpa using h
  have hprev := st395o2_p121
  have hstep := st395o2_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p123 : ((8350310887263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 122, stT395o2 (i+1)) + stT395o2 123 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 122
    simpa using h
  have hprev := st395o2_p122
  have hstep := st395o2_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p124 : ((3820083201061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 123, stT395o2 (i+1)) + stT395o2 124 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 123
    simpa using h
  have hprev := st395o2_p123
  have hstep := st395o2_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p125 : ((8198595638583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 124, stT395o2 (i+1)) + stT395o2 125 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 124
    simpa using h
  have hprev := st395o2_p124
  have hstep := st395o2_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p126 : ((8892790050423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 125, stT395o2 (i+1)) + stT395o2 126 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 125
    simpa using h
  have hprev := st395o2_p125
  have hstep := st395o2_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p127 : ((8343283579889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 126, stT395o2 (i+1)) + stT395o2 127 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 126
    simpa using h
  have hprev := st395o2_p126
  have hstep := st395o2_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p128 : ((7637445637313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 127, stT395o2 (i+1)) + stT395o2 128 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 127
    simpa using h
  have hprev := st395o2_p127
  have hstep := st395o2_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p129 : ((8143341641913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 128, stT395o2 (i+1)) + stT395o2 129 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 128
    simpa using h
  have hprev := st395o2_p128
  have hstep := st395o2_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p130 : ((8883364591761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 129, stT395o2 (i+1)) + stT395o2 130 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 129
    simpa using h
  have hprev := st395o2_p129
  have hstep := st395o2_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p131 : ((8457494563611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 130, stT395o2 (i+1)) + stT395o2 131 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 130
    simpa using h
  have hprev := st395o2_p130
  have hstep := st395o2_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p132 : ((3835019419349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 131, stT395o2 (i+1)) + stT395o2 132 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 131
    simpa using h
  have hprev := st395o2_p131
  have hstep := st395o2_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p133 : ((7975435495607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 132, stT395o2 (i+1)) + stT395o2 133 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 132
    simpa using h
  have hprev := st395o2_p132
  have hstep := st395o2_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p134 : ((8808288906671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 133, stT395o2 (i+1)) + stT395o2 134 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 133
    simpa using h
  have hprev := st395o2_p133
  have hstep := st395o2_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p135 : ((4332935348373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 134, stT395o2 (i+1)) + stT395o2 135 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 134
    simpa using h
  have hprev := st395o2_p134
  have hstep := st395o2_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p136 : ((3904768513641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 135, stT395o2 (i+1)) + stT395o2 136 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 135
    simpa using h
  have hprev := st395o2_p135
  have hstep := st395o2_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p137 : ((3874472978961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 136, stT395o2 (i+1)) + stT395o2 137 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 136
    simpa using h
  have hprev := st395o2_p136
  have hstep := st395o2_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p138 : ((4291135550769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 137, stT395o2 (i+1)) + stT395o2 138 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 137
    simpa using h
  have hprev := st395o2_p137
  have hstep := st395o2_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p139 : ((4436596824111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 138, stT395o2 (i+1)) + stT395o2 139 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 138
    simpa using h
  have hprev := st395o2_p138
  have hstep := st395o2_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p140 : ((8133563856367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 139, stT395o2 (i+1)) + stT395o2 140 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 139
    simpa using h
  have hprev := st395o2_p139
  have hstep := st395o2_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p141 : ((7610371031303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 140, stT395o2 (i+1)) + stT395o2 141 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 140
    simpa using h
  have hprev := st395o2_p140
  have hstep := st395o2_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p142 : ((1633425468823/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 141, stT395o2 (i+1)) + stT395o2 142 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 141
    simpa using h
  have hprev := st395o2_p141
  have hstep := st395o2_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p143 : ((8884049318103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 142, stT395o2 (i+1)) + stT395o2 143 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 142
    simpa using h
  have hprev := st395o2_p142
  have hstep := st395o2_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p144 : ((8601258258537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 143, stT395o2 (i+1)) + stT395o2 144 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 143
    simpa using h
  have hprev := st395o2_p143
  have hstep := st395o2_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p145 : ((7779141026737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 144, stT395o2 (i+1)) + stT395o2 145 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 144
    simpa using h
  have hprev := st395o2_p144
  have hstep := st395o2_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p146 : ((7720203893053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 145, stT395o2 (i+1)) + stT395o2 146 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 145
    simpa using h
  have hprev := st395o2_p145
  have hstep := st395o2_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p147 : ((8509581830073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 146, stT395o2 (i+1)) + stT395o2 147 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 146
    simpa using h
  have hprev := st395o2_p146
  have hstep := st395o2_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p148 : ((1784408067081/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 147, stT395o2 (i+1)) + stT395o2 148 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 147
    simpa using h
  have hprev := st395o2_p147
  have hstep := st395o2_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p149 : ((8331884444941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 148, stT395o2 (i+1)) + stT395o2 149 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 148
    simpa using h
  have hprev := st395o2_p148
  have hstep := st395o2_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p150 : ((3818851389013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 149, stT395o2 (i+1)) + stT395o2 150 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 149
    simpa using h
  have hprev := st395o2_p149
  have hstep := st395o2_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p151 : ((3937539113661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 150, stT395o2 (i+1)) + stT395o2 151 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 150
    simpa using h
  have hprev := st395o2_p150
  have hstep := st395o2_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p152 : ((8685806440353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 151, stT395o2 (i+1)) + stT395o2 152 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 151
    simpa using h
  have hprev := st395o2_p151
  have hstep := st395o2_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p153 : ((8883288627297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 152, stT395o2 (i+1)) + stT395o2 153 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 152
    simpa using h
  have hprev := st395o2_p152
  have hstep := st395o2_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p154 : ((818837185261/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 153, stT395o2 (i+1)) + stT395o2 154 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 153
    simpa using h
  have hprev := st395o2_p153
  have hstep := st395o2_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p155 : ((759917865703/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 154, stT395o2 (i+1)) + stT395o2 155 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 154
    simpa using h
  have hprev := st395o2_p154
  have hstep := st395o2_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p156 : ((794498067751/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 155, stT395o2 (i+1)) + stT395o2 156 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 155
    simpa using h
  have hprev := st395o2_p155
  have hstep := st395o2_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p157 : ((4367728064707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 156, stT395o2 (i+1)) + stT395o2 157 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 156
    simpa using h
  have hprev := st395o2_p156
  have hstep := st395o2_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p158 : ((8877045386489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 157, stT395o2 (i+1)) + stT395o2 158 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 157
    simpa using h
  have hprev := st395o2_p157
  have hstep := st395o2_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p159 : ((8182451585341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 158, stT395o2 (i+1)) + stT395o2 159 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 158
    simpa using h
  have hprev := st395o2_p158
  have hstep := st395o2_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p160 : ((7595697646471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 159, stT395o2 (i+1)) + stT395o2 160 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 159
    simpa using h
  have hprev := st395o2_p159
  have hstep := st395o2_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p161 : ((7898394935271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 160, stT395o2 (i+1)) + stT395o2 161 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 160
    simpa using h
  have hprev := st395o2_p160
  have hstep := st395o2_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p162 : ((8683184266347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 161, stT395o2 (i+1)) + stT395o2 162 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 161
    simpa using h
  have hprev := st395o2_p161
  have hstep := st395o2_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p163 : ((8921348568027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 162, stT395o2 (i+1)) + stT395o2 163 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 162
    simpa using h
  have hprev := st395o2_p162
  have hstep := st395o2_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p164 : ((8310149907823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 163, stT395o2 (i+1)) + stT395o2 164 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 163
    simpa using h
  have hprev := st395o2_p163
  have hstep := st395o2_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p165 : ((1527584449863/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 164, stT395o2 (i+1)) + stT395o2 165 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 164
    simpa using h
  have hprev := st395o2_p164
  have hstep := st395o2_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p166 : ((1550973730113/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 165, stT395o2 (i+1)) + stT395o2 166 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 165
    simpa using h
  have hprev := st395o2_p165
  have hstep := st395o2_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p167 : ((1063461358521/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 166, stT395o2 (i+1)) + stT395o2 167 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 166
    simpa using h
  have hprev := st395o2_p166
  have hstep := st395o2_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p168 : ((1119882323601/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 167, stT395o2 (i+1)) + stT395o2 168 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 167
    simpa using h
  have hprev := st395o2_p167
  have hstep := st395o2_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p169 : ((8558836161049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 168, stT395o2 (i+1)) + stT395o2 169 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 168
    simpa using h
  have hprev := st395o2_p168
  have hstep := st395o2_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p170 : ((7799500928869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 169, stT395o2 (i+1)) + stT395o2 170 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 169
    simpa using h
  have hprev := st395o2_p169
  have hstep := st395o2_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p171 : ((7594814444229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 170, stT395o2 (i+1)) + stT395o2 171 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 170
    simpa using h
  have hprev := st395o2_p170
  have hstep := st395o2_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p172 : ((1636558675041/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 171, stT395o2 (i+1)) + stT395o2 172 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 171
    simpa using h
  have hprev := st395o2_p171
  have hstep := st395o2_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p173 : ((1773149957571/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 172, stT395o2 (i+1)) + stT395o2 173 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 172
    simpa using h
  have hprev := st395o2_p172
  have hstep := st395o2_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p174 : ((4424383047979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 173, stT395o2 (i+1)) + stT395o2 174 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 173
    simpa using h
  have hprev := st395o2_p173
  have hstep := st395o2_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p175 : ((8157462222097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 174, stT395o2 (i+1)) + stT395o2 175 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 174
    simpa using h
  have hprev := st395o2_p174
  have hstep := st395o2_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p176 : ((3792581150179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 175, stT395o2 (i+1)) + stT395o2 176 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 175
    simpa using h
  have hprev := st395o2_p175
  have hstep := st395o2_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p177 : ((486007795717/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 176, stT395o2 (i+1)) + stT395o2 177 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 176
    simpa using h
  have hprev := st395o2_p176
  have hstep := st395o2_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p178 : ((8510499465121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 177, stT395o2 (i+1)) + stT395o2 178 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 177
    simpa using h
  have hprev := st395o2_p177
  have hstep := st395o2_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p179 : ((8971989752041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 178, stT395o2 (i+1)) + stT395o2 179 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 178
    simpa using h
  have hprev := st395o2_p178
  have hstep := st395o2_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p180 : ((1731606030473/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 179, stT395o2 (i+1)) + stT395o2 180 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 179
    simpa using h
  have hprev := st395o2_p179
  have hstep := st395o2_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p181 : ((1583069822807/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 180, stT395o2 (i+1)) + stT395o2 181 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 180
    simpa using h
  have hprev := st395o2_p180
  have hstep := st395o2_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p182 : ((1508818958557/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 181, stT395o2 (i+1)) + stT395o2 182 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 181
    simpa using h
  have hprev := st395o2_p181
  have hstep := st395o2_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p183 : ((3967633815067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 182, stT395o2 (i+1)) + stT395o2 183 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 182
    simpa using h
  have hprev := st395o2_p182
  have hstep := st395o2_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p184 : ((8670969037729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 183, stT395o2 (i+1)) + stT395o2 184 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 183
    simpa using h
  have hprev := st395o2_p183
  have hstep := st395o2_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p185 : ((8982190270427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 184, stT395o2 (i+1)) + stT395o2 185 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 184
    simpa using h
  have hprev := st395o2_p184
  have hstep := st395o2_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p186 : ((1710326524951/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 185, stT395o2 (i+1)) + stT395o2 186 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 185
    simpa using h
  have hprev := st395o2_p185
  have hstep := st395o2_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p187 : ((313008611099/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 186, stT395o2 (i+1)) + stT395o2 187 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 186
    simpa using h
  have hprev := st395o2_p186
  have hstep := st395o2_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p188 : ((301600042681/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 187, stT395o2 (i+1)) + stT395o2 188 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 187
    simpa using h
  have hprev := st395o2_p187
  have hstep := st395o2_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p189 : ((1595573118461/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 188, stT395o2 (i+1)) + stT395o2 189 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 188
    simpa using h
  have hprev := st395o2_p188
  have hstep := st395o2_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p190 : ((8698308965293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 189, stT395o2 (i+1)) + stT395o2 190 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 189
    simpa using h
  have hprev := st395o2_p189
  have hstep := st395o2_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p191 : ((8991074241433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 190, stT395o2 (i+1)) + stT395o2 191 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 190
    simpa using h
  have hprev := st395o2_p190
  have hstep := st395o2_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p192 : ((8574819758481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 191, stT395o2 (i+1)) + stT395o2 192 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 191
    simpa using h
  have hprev := st395o2_p191
  have hstep := st395o2_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p193 : ((7856725558353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 192, stT395o2 (i+1)) + stT395o2 193 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 192
    simpa using h
  have hprev := st395o2_p192
  have hstep := st395o2_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p194 : ((3762505275689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 193, stT395o2 (i+1)) + stT395o2 194 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 193
    simpa using h
  have hprev := st395o2_p193
  have hstep := st395o2_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p195 : ((789020577573/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 194, stT395o2 (i+1)) + stT395o2 195 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 194
    simpa using h
  have hprev := st395o2_p194
  have hstep := st395o2_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p196 : ((860422506171/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 195, stT395o2 (i+1)) + stT395o2 196 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 195
    simpa using h
  have hprev := st395o2_p195
  have hstep := st395o2_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p197 : ((450060275427/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 196, stT395o2 (i+1)) + stT395o2 197 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 196
    simpa using h
  have hprev := st395o2_p196
  have hstep := st395o2_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p198 : ((871857844557/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 197, stT395o2 (i+1)) + stT395o2 198 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 197
    simpa using h
  have hprev := st395o2_p197
  have hstep := st395o2_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p199 : ((1002438687387/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 198, stT395o2 (i+1)) + stT395o2 199 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 198
    simpa using h
  have hprev := st395o2_p198
  have hstep := st395o2_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p200 : ((7538666132491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 199, stT395o2 (i+1)) + stT395o2 200 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 199
    simpa using h
  have hprev := st395o2_p199
  have hstep := st395o2_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p201 : ((1926117013729/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 200, stT395o2 (i+1)) + stT395o2 201 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 200
    simpa using h
  have hprev := st395o2_p200
  have hstep := st395o2_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p202 : ((1672913315517/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 201, stT395o2 (i+1)) + stT395o2 202 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 201
    simpa using h
  have hprev := st395o2_p201
  have hstep := st395o2_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p203 : ((8934950172849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 202, stT395o2 (i+1)) + stT395o2 203 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 202
    simpa using h
  have hprev := st395o2_p202
  have hstep := st395o2_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p204 : ((4459859302697/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 203, stT395o2 (i+1)) + stT395o2 204 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 203
    simpa using h
  have hprev := st395o2_p203
  have hstep := st395o2_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p205 : ((4168371918571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 204, stT395o2 (i+1)) + stT395o2 205 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 204
    simpa using h
  have hprev := st395o2_p204
  have hstep := st395o2_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p206 : ((384454981229/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 205, stT395o2 (i+1)) + stT395o2 206 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 205
    simpa using h
  have hprev := st395o2_p205
  have hstep := st395o2_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p207 : ((7526130790501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 206, stT395o2 (i+1)) + stT395o2 207 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 206
    simpa using h
  have hprev := st395o2_p206
  have hstep := st395o2_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p208 : ((7980783711751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 207, stT395o2 (i+1)) + stT395o2 208 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 207
    simpa using h
  have hprev := st395o2_p207
  have hstep := st395o2_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p209 : ((8669560694107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 208, stT395o2 (i+1)) + stT395o2 209 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 208
    simpa using h
  have hprev := st395o2_p208
  have hstep := st395o2_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p210 : ((4511098510171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 209, stT395o2 (i+1)) + stT395o2 210 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 209
    simpa using h
  have hprev := st395o2_p209
  have hstep := st395o2_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p211 : ((4376462450641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 210, stT395o2 (i+1)) + stT395o2 211 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 210
    simpa using h
  have hprev := st395o2_p210
  have hstep := st395o2_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p212 : ((2021248468529/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 211, stT395o2 (i+1)) + stT395o2 212 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 211
    simpa using h
  have hprev := st395o2_p211
  have hstep := st395o2_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p213 : ((151167234397/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 212, stT395o2 (i+1)) + stT395o2 213 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 212
    simpa using h
  have hprev := st395o2_p212
  have hstep := st395o2_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p214 : ((1518294778733/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 213, stT395o2 (i+1)) + stT395o2 214 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 213
    simpa using h
  have hprev := st395o2_p213
  have hstep := st395o2_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p215 : ((8153718613187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 214, stT395o2 (i+1)) + stT395o2 215 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 214
    simpa using h
  have hprev := st395o2_p214
  have hstep := st395o2_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p216 : ((1760126431909/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 215, stT395o2 (i+1)) + stT395o2 216 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 215
    simpa using h
  have hprev := st395o2_p215
  have hstep := st395o2_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p217 : ((1805860831033/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 216, stT395o2 (i+1)) + stT395o2 217 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 216
    simpa using h
  have hprev := st395o2_p216
  have hstep := st395o2_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p218 : ((8666973754601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 217, stT395o2 (i+1)) + stT395o2 218 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 217
    simpa using h
  have hprev := st395o2_p217
  have hstep := st395o2_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p219 : ((7994746889249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 218, stT395o2 (i+1)) + stT395o2 219 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 218
    simpa using h
  have hprev := st395o2_p218
  have hstep := st395o2_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p220 : ((7523684697649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 219, stT395o2 (i+1)) + stT395o2 220 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 219
    simpa using h
  have hprev := st395o2_p219
  have hstep := st395o2_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p221 : ((7605644399473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 220, stT395o2 (i+1)) + stT395o2 221 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 220
    simpa using h
  have hprev := st395o2_p220
  have hstep := st395o2_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p222 : ((8175330337301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 221, stT395o2 (i+1)) + stT395o2 222 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 221
    simpa using h
  have hprev := st395o2_p221
  have hstep := st395o2_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p223 : ((4404333140489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 222, stT395o2 (i+1)) + stT395o2 223 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 222
    simpa using h
  have hprev := st395o2_p222
  have hstep := st395o2_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p224 : ((9041781521913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 223, stT395o2 (i+1)) + stT395o2 224 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 223
    simpa using h
  have hprev := st395o2_p223
  have hstep := st395o2_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p225 : ((2177146838829/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 224, stT395o2 (i+1)) + stT395o2 225 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 224
    simpa using h
  have hprev := st395o2_p224
  have hstep := st395o2_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p226 : ((4026570701733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 225, stT395o2 (i+1)) + stT395o2 226 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 225
    simpa using h
  have hprev := st395o2_p225
  have hstep := st395o2_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p227 : ((754559232439/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 226, stT395o2 (i+1)) + stT395o2 227 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 226
    simpa using h
  have hprev := st395o2_p226
  have hstep := st395o2_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p228 : ((3771996143659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 227, stT395o2 (i+1)) + stT395o2 228 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 227
    simpa using h
  have hprev := st395o2_p227
  have hstep := st395o2_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p229 : ((4022802346561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 228, stT395o2 (i+1)) + stT395o2 229 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 228
    simpa using h
  have hprev := st395o2_p228
  have hstep := st395o2_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p230 : ((4348687394271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 229, stT395o2 (i+1)) + stT395o2 230 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 229
    simpa using h
  have hprev := st395o2_p229
  have hstep := st395o2_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p231 : ((9048072540807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 230, stT395o2 (i+1)) + stT395o2 231 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 230
    simpa using h
  have hprev := st395o2_p230
  have hstep := st395o2_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p232 : ((8859735545229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 231, stT395o2 (i+1)) + stT395o2 232 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 231
    simpa using h
  have hprev := st395o2_p231
  have hstep := st395o2_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p233 : ((1652867286423/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 232, stT395o2 (i+1)) + stT395o2 233 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 232
    simpa using h
  have hprev := st395o2_p232
  have hstep := st395o2_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p234 : ((479136234747/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 233, stT395o2 (i+1)) + stT395o2 234 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 233
    simpa using h
  have hprev := st395o2_p233
  have hstep := st395o2_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p235 : ((7465179578169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 234, stT395o2 (i+1)) + stT395o2 235 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 234
    simpa using h
  have hprev := st395o2_p234
  have hstep := st395o2_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p236 : ((7791674862137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 235, stT395o2 (i+1)) + stT395o2 236 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 235
    simpa using h
  have hprev := st395o2_p235
  have hstep := st395o2_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p237 : ((1685381834689/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 236, stT395o2 (i+1)) + stT395o2 237 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 236
    simpa using h
  have hprev := st395o2_p236
  have hstep := st395o2_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p238 : ((1119241246799/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 237, stT395o2 (i+1)) + stT395o2 238 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 237
    simpa using h
  have hprev := st395o2_p237
  have hstep := st395o2_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p239 : ((4516102727849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 238, stT395o2 (i+1)) + stT395o2 239 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 238
    simpa using h
  have hprev := st395o2_p238
  have hstep := st395o2_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p240 : ((2153678371687/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 239, stT395o2 (i+1)) + stT395o2 240 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 239
    simpa using h
  have hprev := st395o2_p239
  have hstep := st395o2_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p241 : ((3985607407601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 240, stT395o2 (i+1)) + stT395o2 241 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 240
    simpa using h
  have hprev := st395o2_p240
  have hstep := st395o2_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p242 : ((3755181643751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 241, stT395o2 (i+1)) + stT395o2 242 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 241
    simpa using h
  have hprev := st395o2_p241
  have hstep := st395o2_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p243 : ((3760019516001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 242, stT395o2 (i+1)) + stT395o2 243 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 242
    simpa using h
  have hprev := st395o2_p242
  have hstep := st395o2_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p244 : ((3995392766361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 243, stT395o2 (i+1)) + stT395o2 244 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 243
    simpa using h
  have hprev := st395o2_p243
  have hstep := st395o2_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p245 : ((4314177196213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 244, stT395o2 (i+1)) + stT395o2 245 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 244
    simpa using h
  have hprev := st395o2_p244
  have hstep := st395o2_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p246 : ((4520288621249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 245, stT395o2 (i+1)) + stT395o2 246 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 245
    simpa using h
  have hprev := st395o2_p245
  have hstep := st395o2_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p247 : ((4489111928819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 246, stT395o2 (i+1)) + stT395o2 247 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 246
    simpa using h
  have hprev := st395o2_p246
  have hstep := st395o2_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p248 : ((4241164358351/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 247, stT395o2 (i+1)) + stT395o2 248 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 247
    simpa using h
  have hprev := st395o2_p247
  have hstep := st395o2_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p249 : ((7853132949277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 248, stT395o2 (i+1)) + stT395o2 249 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 248
    simpa using h
  have hprev := st395o2_p248
  have hstep := st395o2_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p250 : ((7465756179101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 249, stT395o2 (i+1)) + stT395o2 250 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 249
    simpa using h
  have hprev := st395o2_p249
  have hstep := st395o2_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p251 : ((7547091837941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 250, stT395o2 (i+1)) + stT395o2 251 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 250
    simpa using h
  have hprev := st395o2_p250
  have hstep := st395o2_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p252 : ((8046154243661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 251, stT395o2 (i+1)) + stT395o2 252 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 251
    simpa using h
  have hprev := st395o2_p251
  have hstep := st395o2_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p253 : ((346793527247/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 252, stT395o2 (i+1)) + stT395o2 253 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 252
    simpa using h
  have hprev := st395o2_p252
  have hstep := st395o2_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p254 : ((1811472383727/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 253, stT395o2 (i+1)) + stT395o2 254 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 253
    simpa using h
  have hprev := st395o2_p253
  have hstep := st395o2_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p255 : ((898841642481/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 254, stT395o2 (i+1)) + stT395o2 255 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 254
    simpa using h
  have hprev := st395o2_p254
  have hstep := st395o2_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p256 : ((1701075005389/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 255, stT395o2 (i+1)) + stT395o2 256 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 255
    simpa using h
  have hprev := st395o2_p255
  have hstep := st395o2_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p257 : ((7883679204863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 256, stT395o2 (i+1)) + stT395o2 257 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 256
    simpa using h
  have hprev := st395o2_p256
  have hstep := st395o2_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p258 : ((7472495886429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 257, stT395o2 (i+1)) + stT395o2 258 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 257
    simpa using h
  have hprev := st395o2_p257
  have hstep := st395o2_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p259 : ((468685504371/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 258, stT395o2 (i+1)) + stT395o2 259 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 258
    simpa using h
  have hprev := st395o2_p258
  have hstep := st395o2_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p260 : ((7945439915231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 259, stT395o2 (i+1)) + stT395o2 260 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 259
    simpa using h
  have hprev := st395o2_p259
  have hstep := st395o2_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p261 : ((1712873765131/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 260, stT395o2 (i+1)) + stT395o2 261 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 260
    simpa using h
  have hprev := st395o2_p260
  have hstep := st395o2_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p262 : ((9017898509459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 261, stT395o2 (i+1)) + stT395o2 262 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 261
    simpa using h
  have hprev := st395o2_p261
  have hstep := st395o2_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p263 : ((9062251801013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 262, stT395o2 (i+1)) + stT395o2 263 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 262
    simpa using h
  have hprev := st395o2_p262
  have hstep := st395o2_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p264 : ((8676427335393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 263, stT395o2 (i+1)) + stT395o2 264 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 263
    simpa using h
  have hprev := st395o2_p263
  have hstep := st395o2_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p265 : ((8068691402377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 264, stT395o2 (i+1)) + stT395o2 265 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 264
    simpa using h
  have hprev := st395o2_p264
  have hstep := st395o2_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p266 : ((7561669994737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 265, stT395o2 (i+1)) + stT395o2 266 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 265
    simpa using h
  have hprev := st395o2_p265
  have hstep := st395o2_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p267 : ((3710329656227/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 266, stT395o2 (i+1)) + stT395o2 267 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 266
    simpa using h
  have hprev := st395o2_p266
  have hstep := st395o2_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p268 : ((1543324524993/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 267, stT395o2 (i+1)) + stT395o2 268 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 267
    simpa using h
  have hprev := st395o2_p267
  have hstep := st395o2_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p269 : ((1658705801509/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 268, stT395o2 (i+1)) + stT395o2 269 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 268
    simpa using h
  have hprev := st395o2_p268
  have hstep := st395o2_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p270 : ((1770641920909/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 269, stT395o2 (i+1)) + stT395o2 270 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 269
    simpa using h
  have hprev := st395o2_p269
  have hstep := st395o2_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p271 : ((1822073398061/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 270, stT395o2 (i+1)) + stT395o2 271 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 270
    simpa using h
  have hprev := st395o2_p270
  have hstep := st395o2_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p272 : ((1787361039401/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 271, stT395o2 (i+1)) + stT395o2 272 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 271
    simpa using h
  have hprev := st395o2_p271
  have hstep := st395o2_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p273 : ((8422639196657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 272, stT395o2 (i+1)) + stT395o2 273 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 272
    simpa using h
  have hprev := st395o2_p272
  have hstep := st395o2_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p274 : ((1565365302529/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 273, stT395o2 (i+1)) + stT395o2 274 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 273
    simpa using h
  have hprev := st395o2_p273
  have hstep := st395o2_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p275 : ((3722649040853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 274, stT395o2 (i+1)) + stT395o2 275 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 274
    simpa using h
  have hprev := st395o2_p274
  have hstep := st395o2_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p276 : ((7464480957007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 275, stT395o2 (i+1)) + stT395o2 276 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 275
    simpa using h
  have hprev := st395o2_p275
  have hstep := st395o2_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p277 : ((7872343844627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 276, stT395o2 (i+1)) + stT395o2 277 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 276
    simpa using h
  have hprev := st395o2_p276
  have hstep := st395o2_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p278 : ((8468258183507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 277, stT395o2 (i+1)) + stT395o2 278 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 277
    simpa using h
  have hprev := st395o2_p277
  have hstep := st395o2_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p279 : ((8963597351427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 278, stT395o2 (i+1)) + stT395o2 279 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 278
    simpa using h
  have hprev := st395o2_p278
  have hstep := st395o2_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p280 : ((9121748725159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 279, stT395o2 (i+1)) + stT395o2 280 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 279
    simpa using h
  have hprev := st395o2_p279
  have hstep := st395o2_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p281 : ((8869673539909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 280, stT395o2 (i+1)) + stT395o2 281 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 280
    simpa using h
  have hprev := st395o2_p280
  have hstep := st395o2_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p282 : ((8329106744529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 281, stT395o2 (i+1)) + stT395o2 282 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 281
    simpa using h
  have hprev := st395o2_p281
  have hstep := st395o2_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p283 : ((3877781434909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 282, stT395o2 (i+1)) + stT395o2 283 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 282
    simpa using h
  have hprev := st395o2_p282
  have hstep := st395o2_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p284 : ((7416565118819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 283, stT395o2 (i+1)) + stT395o2 284 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 283
    simpa using h
  have hprev := st395o2_p283
  have hstep := st395o2_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p285 : ((7467519486127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 284, stT395o2 (i+1)) + stT395o2 285 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 284
    simpa using h
  have hprev := st395o2_p284
  have hstep := st395o2_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p286 : ((7882489238863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 285, stT395o2 (i+1)) + stT395o2 286 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 285
    simpa using h
  have hprev := st395o2_p285
  have hstep := st395o2_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p287 : ((66168619623/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 286, stT395o2 (i+1)) + stT395o2 287 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 286
    simpa using h
  have hprev := st395o2_p286
  have hstep := st395o2_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p288 : ((4480661250897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 287, stT395o2 (i+1)) + stT395o2 288 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 287
    simpa using h
  have hprev := st395o2_p287
  have hstep := st395o2_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p289 : ((9136678296469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 288, stT395o2 (i+1)) + stT395o2 289 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 288
    simpa using h
  have hprev := st395o2_p288
  have hstep := st395o2_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p290 : ((1783825636743/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 289, stT395o2 (i+1)) + stT395o2 290 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 289
    simpa using h
  have hprev := st395o2_p289
  have hstep := st395o2_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p291 : ((1050988674789/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 290, stT395o2 (i+1)) + stT395o2 291 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 290
    simpa using h
  have hprev := st395o2_p290
  have hstep := st395o2_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p292 : ((3915362408477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 291, stT395o2 (i+1)) + stT395o2 292 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 291
    simpa using h
  have hprev := st395o2_p291
  have hstep := st395o2_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p293 : ((7441316383241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 292, stT395o2 (i+1)) + stT395o2 293 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 292
    simpa using h
  have hprev := st395o2_p292
  have hstep := st395o2_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p294 : ((7408286754833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 293, stT395o2 (i+1)) + stT395o2 294 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 293
    simpa using h
  have hprev := st395o2_p293
  have hstep := st395o2_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p295 : ((7743707760143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 294, stT395o2 (i+1)) + stT395o2 295 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 294
    simpa using h
  have hprev := st395o2_p294
  have hstep := st395o2_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p296 : ((8300908662653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 295, stT395o2 (i+1)) + stT395o2 296 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 295
    simpa using h
  have hprev := st395o2_p295
  have hstep := st395o2_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p297 : ((1768048097131/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 296, stT395o2 (i+1)) + stT395o2 297 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 296
    simpa using h
  have hprev := st395o2_p296
  have hstep := st395o2_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p298 : ((9132684482363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 297, stT395o2 (i+1)) + stT395o2 298 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 297
    simpa using h
  have hprev := st395o2_p297
  have hstep := st395o2_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p299 : ((1132039242301/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 298, stT395o2 (i+1)) + stT395o2 299 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 298
    simpa using h
  have hprev := st395o2_p298
  have hstep := st395o2_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p300 : ((108067751999/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 299, stT395o2 (i+1)) + stT395o2 300 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 299
    simpa using h
  have hprev := st395o2_p299
  have hstep := st395o2_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p301 : ((807326563377/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 300, stT395o2 (i+1)) + stT395o2 301 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 300
    simpa using h
  have hprev := st395o2_p300
  have hstep := st395o2_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p302 : ((3788860433133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 301, stT395o2 (i+1)) + stT395o2 302 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 301
    simpa using h
  have hprev := st395o2_p301
  have hstep := st395o2_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p303 : ((7362172370811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 302, stT395o2 (i+1)) + stT395o2 303 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 302
    simpa using h
  have hprev := st395o2_p302
  have hstep := st395o2_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p304 : ((234781642321/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 303, stT395o2 (i+1)) + stT395o2 304 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 303
    simpa using h
  have hprev := st395o2_p303
  have hstep := st395o2_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p305 : ((3983361874663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 304, stT395o2 (i+1)) + stT395o2 305 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 304
    simpa using h
  have hprev := st395o2_p304
  have hstep := st395o2_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p306 : ((8538330441531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 305, stT395o2 (i+1)) + stT395o2 306 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 305
    simpa using h
  have hprev := st395o2_p305
  have hstep := st395o2_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p307 : ((8997836579131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 306, stT395o2 (i+1)) + stT395o2 307 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 306
    simpa using h
  have hprev := st395o2_p306
  have hstep := st395o2_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p308 : ((9162758930407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 307, stT395o2 (i+1)) + stT395o2 308 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 307
    simpa using h
  have hprev := st395o2_p307
  have hstep := st395o2_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p309 : ((1793906334437/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 308, stT395o2 (i+1)) + stT395o2 309 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 308
    simpa using h
  have hprev := st395o2_p308
  have hstep := st395o2_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p310 : ((8496353442593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 309, stT395o2 (i+1)) + stT395o2 310 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 309
    simpa using h
  have hprev := st395o2_p309
  have hstep := st395o2_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p311 : ((7929983632001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 310, stT395o2 (i+1)) + stT395o2 311 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 310
    simpa using h
  have hprev := st395o2_p310
  have hstep := st395o2_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p312 : ((1498228876597/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 311, stT395o2 (i+1)) + stT395o2 312 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 311
    simpa using h
  have hprev := st395o2_p311
  have hstep := st395o2_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p313 : ((7348613281843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 312, stT395o2 (i+1)) + stT395o2 313 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 312
    simpa using h
  have hprev := st395o2_p312
  have hstep := st395o2_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p314 : ((1511069681879/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 313, stT395o2 (i+1)) + stT395o2 314 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 313
    simpa using h
  have hprev := st395o2_p313
  have hstep := st395o2_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p315 : ((8030380737559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 314, stT395o2 (i+1)) + stT395o2 315 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 314
    simpa using h
  have hprev := st395o2_p314
  have hstep := st395o2_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p316 : ((8591939287309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 315, stT395o2 (i+1)) + stT395o2 316 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 315
    simpa using h
  have hprev := st395o2_p315
  have hstep := st395o2_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p317 : ((9027820636539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 316, stT395o2 (i+1)) + stT395o2 317 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 316
    simpa using h
  have hprev := st395o2_p316
  have hstep := st395o2_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p318 : ((9175441061679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 317, stT395o2 (i+1)) + stT395o2 318 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 317
    simpa using h
  have hprev := st395o2_p317
  have hstep := st395o2_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p319 : ((4490747903079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 318, stT395o2 (i+1)) + stT395o2 319 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 318
    simpa using h
  have hprev := st395o2_p318
  have hstep := st395o2_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p320 : ((8519771801889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 319, stT395o2 (i+1)) + stT395o2 320 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 319
    simpa using h
  have hprev := st395o2_p319
  have hstep := st395o2_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p321 : ((7961681058343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 320, stT395o2 (i+1)) + stT395o2 321 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 320
    simpa using h
  have hprev := st395o2_p320
  have hstep := st395o2_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p322 : ((3755934148991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 321, stT395o2 (i+1)) + stT395o2 322 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 321
    simpa using h
  have hprev := st395o2_p321
  have hstep := st395o2_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p323 : ((1833301694993/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 322, stT395o2 (i+1)) + stT395o2 323 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 322
    simpa using h
  have hprev := st395o2_p322
  have hstep := st395o2_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p324 : ((7488673846727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 323, stT395o2 (i+1)) + stT395o2 324 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 323
    simpa using h
  have hprev := st395o2_p323
  have hstep := st395o2_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p325 : ((7920488382227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 324, stT395o2 (i+1)) + stT395o2 325 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 324
    simpa using h
  have hprev := st395o2_p324
  have hstep := st395o2_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p326 : ((8472884192771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 325, stT395o2 (i+1)) + stT395o2 326 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 325
    simpa using h
  have hprev := st395o2_p325
  have hstep := st395o2_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p327 : ((357964128637/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 326, stT395o2 (i+1)) + stT395o2 327 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 326
    simpa using h
  have hprev := st395o2_p326
  have hstep := st395o2_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p328 : ((9181543643901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 327, stT395o2 (i+1)) + stT395o2 328 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 327
    simpa using h
  have hprev := st395o2_p327
  have hstep := st395o2_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p329 : ((1818013571741/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 328, stT395o2 (i+1)) + stT395o2 329 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 328
    simpa using h
  have hprev := st395o2_p328
  have hstep := st395o2_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p330 : ((8708400522199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 329, stT395o2 (i+1)) + stT395o2 330 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 329
    simpa using h
  have hprev := st395o2_p329
  have hstep := st395o2_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p331 : ((8170477854599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 330, stT395o2 (i+1)) + stT395o2 331 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 330
    simpa using h
  have hprev := st395o2_p330
  have hstep := st395o2_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p332 : ((7662546935353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 331, stT395o2 (i+1)) + stT395o2 332 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 331
    simpa using h
  have hprev := st395o2_p331
  have hstep := st395o2_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p333 : ((919805664519/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 332, stT395o2 (i+1)) + stT395o2 333 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 332
    simpa using h
  have hprev := st395o2_p332
  have hstep := st395o2_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p334 : ((1840149202063/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 333, stT395o2 (i+1)) + stT395o2 334 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 333
    simpa using h
  have hprev := st395o2_p333
  have hstep := st395o2_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p335 : ((3833274546441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 334, stT395o2 (i+1)) + stT395o2 335 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 334
    simpa using h
  have hprev := st395o2_p334
  have hstep := st395o2_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p336 : ((4085788042773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 335, stT395o2 (i+1)) + stT395o2 336 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 335
    simpa using h
  have hprev := st395o2_p335
  have hstep := st395o2_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p337 : ((1088188433199/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 336, stT395o2 (i+1)) + stT395o2 337 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 336
    simpa using h
  have hprev := st395o2_p336
  have hstep := st395o2_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p338 : ((1136309743359/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 337, stT395o2 (i+1)) + stT395o2 338 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 337
    simpa using h
  have hprev := st395o2_p337
  have hstep := st395o2_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p339 : ((9199906228747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 338, stT395o2 (i+1)) + stT395o2 339 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 338
    simpa using h
  have hprev := st395o2_p338
  have hstep := st395o2_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p340 : ((8999314656603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 339, stT395o2 (i+1)) + stT395o2 340 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 339
    simpa using h
  have hprev := st395o2_p339
  have hstep := st395o2_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p341 : ((427801600067/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 340, stT395o2 (i+1)) + stT395o2 341 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 340
    simpa using h
  have hprev := st395o2_p340
  have hstep := st395o2_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p342 : ((320622859277/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 341, stT395o2 (i+1)) + stT395o2 342 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 341
    simpa using h
  have hprev := st395o2_p341
  have hstep := st395o2_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p343 : ((302130586883/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 342, stT395o2 (i+1)) + stT395o2 343 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 342
    simpa using h
  have hprev := st395o2_p342
  have hstep := st395o2_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p344 : ((7317354003039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 343, stT395o2 (i+1)) + stT395o2 344 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 343
    simpa using h
  have hprev := st395o2_p343
  have hstep := st395o2_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p345 : ((1476407665333/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 344, stT395o2 (i+1)) + stT395o2 345 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 344
    simpa using h
  have hprev := st395o2_p344
  have hstep := st395o2_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p346 : ((772509086501/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 345, stT395o2 (i+1)) + stT395o2 346 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 345
    simpa using h
  have hprev := st395o2_p345
  have hstep := st395o2_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p347 : ((164730323281/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 346, stT395o2 (i+1)) + stT395o2 347 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 346
    simpa using h
  have hprev := st395o2_p346
  have hstep := st395o2_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p348 : ((4377288650093/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 347, stT395o2 (i+1)) + stT395o2 348 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 347
    simpa using h
  have hprev := st395o2_p347
  have hstep := st395o2_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p349 : ((569827073257/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 348, stT395o2 (i+1)) + stT395o2 349 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 348
    simpa using h
  have hprev := st395o2_p348
  have hstep := st395o2_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p350 : ((4606276438403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 349, stT395o2 (i+1)) + stT395o2 350 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 349
    simpa using h
  have hprev := st395o2_p349
  have hstep := st395o2_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p351 : ((281640234727/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 350, stT395o2 (i+1)) + stT395o2 351 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 350
    simpa using h
  have hprev := st395o2_p350
  have hstep := st395o2_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p352 : ((4290073334989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 351, stT395o2 (i+1)) + stT395o2 352 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 351
    simpa using h
  have hprev := st395o2_p351
  have hstep := st395o2_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p353 : ((8048979599141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 352, stT395o2 (i+1)) + stT395o2 353 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 352
    simpa using h
  have hprev := st395o2_p352
  have hstep := st395o2_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p354 : ((7581056716091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 353, stT395o2 (i+1)) + stT395o2 354 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 353
    simpa using h
  have hprev := st395o2_p353
  have hstep := st395o2_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p355 : ((1829389303799/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 354, stT395o2 (i+1)) + stT395o2 355 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 354
    simpa using h
  have hprev := st395o2_p354
  have hstep := st395o2_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p356 : ((3668328906559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 355, stT395o2 (i+1)) + stT395o2 356 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 355
    simpa using h
  have hprev := st395o2_p355
  have hstep := st395o2_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p357 : ((3815562897827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 356, stT395o2 (i+1)) + stT395o2 357 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 356
    simpa using h
  have hprev := st395o2_p356
  have hstep := st395o2_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p358 : ((4055942016431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 357, stT395o2 (i+1)) + stT395o2 358 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 357
    simpa using h
  have hprev := st395o2_p357
  have hstep := st395o2_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p359 : ((8635672495843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 358, stT395o2 (i+1)) + stT395o2 359 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 358
    simpa using h
  have hprev := st395o2_p358
  have hstep := st395o2_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p360 : ((9048091788349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 359, stT395o2 (i+1)) + stT395o2 360 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 359
    simpa using h
  have hprev := st395o2_p359
  have hstep := st395o2_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p361 : ((9228994674889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 360, stT395o2 (i+1)) + stT395o2 361 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 360
    simpa using h
  have hprev := st395o2_p360
  have hstep := st395o2_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p362 : ((570431878063/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 361, stT395o2 (i+1)) + stT395o2 362 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 361
    simpa using h
  have hprev := st395o2_p361
  have hstep := st395o2_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p363 : ((548304989591/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 362, stT395o2 (i+1)) + stT395o2 363 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 362
    simpa using h
  have hprev := st395o2_p362
  have hstep := st395o2_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p364 : ((827018371673/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 363, stT395o2 (i+1)) + stT395o2 364 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 363
    simpa using h
  have hprev := st395o2_p363
  have hstep := st395o2_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p365 : ((3881804105933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 364, stT395o2 (i+1)) + stT395o2 365 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 364
    simpa using h
  have hprev := st395o2_p364
  have hstep := st395o2_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p366 : ((7397526350171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 365, stT395o2 (i+1)) + stT395o2 366 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 365
    simpa using h
  have hprev := st395o2_p365
  have hstep := st395o2_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p367 : ((1454993799463/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 366, stT395o2 (i+1)) + stT395o2 367 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 366
    simpa using h
  have hprev := st395o2_p366
  have hstep := st395o2_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p368 : ((1485845590087/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 367, stT395o2 (i+1)) + stT395o2 368 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 367
    simpa using h
  have hprev := st395o2_p367
  have hstep := st395o2_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p369 : ((1953900811493/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 368, stT395o2 (i+1)) + stT395o2 369 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 368
    simpa using h
  have hprev := st395o2_p368
  have hstep := st395o2_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p370 : ((8325104140347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 369, stT395o2 (i+1)) + stT395o2 370 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 369
    simpa using h
  have hprev := st395o2_p369
  have hstep := st395o2_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p371 : ((1763139729999/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 370, stT395o2 (i+1)) + stT395o2 371 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 370
    simpa using h
  have hprev := st395o2_p370
  have hstep := st395o2_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p372 : ((1830408957789/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 371, stT395o2 (i+1)) + stT395o2 372 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 371
    simpa using h
  have hprev := st395o2_p371
  have hstep := st395o2_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p373 : ((1848511271481/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 372, stT395o2 (i+1)) + stT395o2 373 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 372
    simpa using h
  have hprev := st395o2_p372
  have hstep := st395o2_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p374 : ((1812752567929/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 373, stT395o2 (i+1)) + stT395o2 374 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 373
    simpa using h
  have hprev := st395o2_p373
  have hstep := st395o2_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p375 : ((8665600358521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 374, stT395o2 (i+1)) + stT395o2 375 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 374
    simpa using h
  have hprev := st395o2_p374
  have hstep := st395o2_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p376 : ((8156820514361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 375, stT395o2 (i+1)) + stT395o2 376 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 375
    simpa using h
  have hprev := st395o2_p375
  have hstep := st395o2_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p377 : ((7674803654899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 376, stT395o2 (i+1)) + stT395o2 377 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 376
    simpa using h
  have hprev := st395o2_p376
  have hstep := st395o2_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p378 : ((918546246443/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 377, stT395o2 (i+1)) + stT395o2 378 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 377
    simpa using h
  have hprev := st395o2_p377
  have hstep := st395o2_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p379 : ((3631812420599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 378, stT395o2 (i+1)) + stT395o2 379 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 378
    simpa using h
  have hprev := st395o2_p378
  have hstep := st395o2_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p380 : ((930222085887/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 379, stT395o2 (i+1)) + stT395o2 380 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 379
    simpa using h
  have hprev := st395o2_p379
  have hstep := st395o2_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p381 : ((7834572183801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 380, stT395o2 (i+1)) + stT395o2 381 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 380
    simpa using h
  have hprev := st395o2_p380
  have hstep := st395o2_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p382 : ((1667597380341/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 381, stT395o2 (i+1)) + stT395o2 382 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 381
    simpa using h
  have hprev := st395o2_p381
  have hstep := st395o2_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p383 : ((8820193930953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 382, stT395o2 (i+1)) + stT395o2 383 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 382
    simpa using h
  have hprev := st395o2_p382
  have hstep := st395o2_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p384 : ((9156193261773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 383, stT395o2 (i+1)) + stT395o2 384 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 383
    simpa using h
  have hprev := st395o2_p383
  have hstep := st395o2_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p385 : ((4629989652897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 384, stT395o2 (i+1)) + stT395o2 385 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 384
    simpa using h
  have hprev := st395o2_p384
  have hstep := st395o2_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p386 : ((4553023692679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 385, stT395o2 (i+1)) + stT395o2 386 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 385
    simpa using h
  have hprev := st395o2_p385
  have hstep := st395o2_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p387 : ((174699832303/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 386, stT395o2 (i+1)) + stT395o2 387 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 386
    simpa using h
  have hprev := st395o2_p386
  have hstep := st395o2_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p388 : ((1030274882889/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 387, stT395o2 (i+1)) + stT395o2 388 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 387
    simpa using h
  have hprev := st395o2_p387
  have hstep := st395o2_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p389 : ((1938227400381/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 388, stT395o2 (i+1)) + stT395o2 389 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 388
    simpa using h
  have hprev := st395o2_p388
  have hstep := st395o2_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p390 : ((1847559320031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 389, stT395o2 (i+1)) + stT395o2 390 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 389
    simpa using h
  have hprev := st395o2_p389
  have hstep := st395o2_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p391 : ((1811092212333/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 390, stT395o2 (i+1)) + stT395o2 391 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 390
    simpa using h
  have hprev := st395o2_p390
  have hstep := st395o2_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p392 : ((1837646583033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 391, stT395o2 (i+1)) + stT395o2 392 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 391
    simpa using h
  have hprev := st395o2_p391
  have hstep := st395o2_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p393 : ((1536264675469/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 392, stT395o2 (i+1)) + stT395o2 393 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 392
    simpa using h
  have hprev := st395o2_p392
  have hstep := st395o2_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p394 : ((1630778573629/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 393, stT395o2 (i+1)) + stT395o2 394 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 393
    simpa using h
  have hprev := st395o2_p393
  have hstep := st395o2_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p395 : ((8651605760789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 394, stT395o2 (i+1)) + stT395o2 395 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 394
    simpa using h
  have hprev := st395o2_p394
  have hstep := st395o2_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p396 : ((9052768895297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 395, stT395o2 (i+1)) + stT395o2 396 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 395
    simpa using h
  have hprev := st395o2_p395
  have hstep := st395o2_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p397 : ((4630175520361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 396, stT395o2 (i+1)) + stT395o2 397 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 396
    simpa using h
  have hprev := st395o2_p396
  have hstep := st395o2_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p398 : ((9225064192487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 397, stT395o2 (i+1)) + stT395o2 398 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 397
    simpa using h
  have hprev := st395o2_p397
  have hstep := st395o2_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p399 : ((8956567919847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 398, stT395o2 (i+1)) + stT395o2 399 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 398
    simpa using h
  have hprev := st395o2_p398
  have hstep := st395o2_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p400 : ((8520273047259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 399, stT395o2 (i+1)) + stT395o2 400 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 399
    simpa using h
  have hprev := st395o2_p399
  have hstep := st395o2_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p401 : ((4010472742791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 400, stT395o2 (i+1)) + stT395o2 401 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 400
    simpa using h
  have hprev := st395o2_p400
  have hstep := st395o2_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p402 : ((947161492559/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 401, stT395o2 (i+1)) + stT395o2 402 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 401
    simpa using h
  have hprev := st395o2_p401
  have hstep := st395o2_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p403 : ((455858842009/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 402, stT395o2 (i+1)) + stT395o2 403 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 402
    simpa using h
  have hprev := st395o2_p402
  have hstep := st395o2_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p404 : ((7236116333969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 403, stT395o2 (i+1)) + stT395o2 404 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 403
    simpa using h
  have hprev := st395o2_p403
  have hstep := st395o2_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p405 : ((3708404821993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 404, stT395o2 (i+1)) + stT395o2 405 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 404
    simpa using h
  have hprev := st395o2_p404
  have hstep := st395o2_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p406 : ((487041358543/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 405, stT395o2 (i+1)) + stT395o2 406 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 405
    simpa using h
  have hprev := st395o2_p405
  have hstep := st395o2_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p407 : ((8275749960883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 406, stT395o2 (i+1)) + stT395o2 407 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 406
    simpa using h
  have hprev := st395o2_p406
  have hstep := st395o2_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p408 : ((1094285754683/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 407, stT395o2 (i+1)) + stT395o2 408 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 407
    simpa using h
  have hprev := st395o2_p407
  have hstep := st395o2_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p409 : ((2279645716031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 408, stT395o2 (i+1)) + stT395o2 409 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 408
    simpa using h
  have hprev := st395o2_p408
  have hstep := st395o2_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p410 : ((92860565913/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 409, stT395o2 (i+1)) + stT395o2 410 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 409
    simpa using h
  have hprev := st395o2_p409
  have hstep := st395o2_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p411 : ((2304897810089/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 410, stT395o2 (i+1)) + stT395o2 411 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 410
    simpa using h
  have hprev := st395o2_p410
  have hstep := st395o2_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p412 : ((4467649451053/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 411, stT395o2 (i+1)) + stT395o2 412 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 411
    simpa using h
  have hprev := st395o2_p411
  have hstep := st395o2_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p413 : ((169962500481/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 412, stT395o2 (i+1)) + stT395o2 413 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 412
    simpa using h
  have hprev := st395o2_p412
  have hstep := st395o2_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p414 : ((160132529007/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 413, stT395o2 (i+1)) + stT395o2 414 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 413
    simpa using h
  have hprev := st395o2_p413
  have hstep := st395o2_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p415 : ((1892637587619/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 414, stT395o2 (i+1)) + stT395o2 415 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 414
    simpa using h
  have hprev := st395o2_p414
  have hstep := st395o2_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p416 : ((3643160896851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 415, stT395o2 (i+1)) + stT395o2 416 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 415
    simpa using h
  have hprev := st395o2_p415
  have hstep := st395o2_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p417 : ((1803991540923/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 416, stT395o2 (i+1)) + stT395o2 417 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 416
    simpa using h
  have hprev := st395o2_p416
  have hstep := st395o2_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p418 : ((1843485620713/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 417, stT395o2 (i+1)) + stT395o2 418 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 417
    simpa using h
  have hprev := st395o2_p417
  have hstep := st395o2_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p419 : ((7724661330407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 418, stT395o2 (i+1)) + stT395o2 419 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 418
    simpa using h
  have hprev := st395o2_p418
  have hstep := st395o2_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p420 : ((8190917561357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 419, stT395o2 (i+1)) + stT395o2 420 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 419
    simpa using h
  have hprev := st395o2_p419
  have hstep := st395o2_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p421 : ((8671193403637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 420, stT395o2 (i+1)) + stT395o2 421 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 420
    simpa using h
  have hprev := st395o2_p420
  have hstep := st395o2_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p422 : ((1812376488041/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 421, stT395o2 (i+1)) + stT395o2 422 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 421
    simpa using h
  have hprev := st395o2_p421
  have hstep := st395o2_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p423 : ((9279560857189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 422, stT395o2 (i+1)) + stT395o2 423 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 422
    simpa using h
  have hprev := st395o2_p422
  have hstep := st395o2_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p424 : ((4639255691333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 423, stT395o2 (i+1)) + stT395o2 424 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 423
    simpa using h
  have hprev := st395o2_p423
  have hstep := st395o2_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p425 : ((4529973335381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 424, stT395o2 (i+1)) + stT395o2 425 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 424
    simpa using h
  have hprev := st395o2_p424
  have hstep := st395o2_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p426 : ((86710945711/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 425, stT395o2 (i+1)) + stT395o2 426 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 425
    simpa using h
  have hprev := st395o2_p425
  have hstep := st395o2_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p427 : ((2048657160147/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 426, stT395o2 (i+1)) + stT395o2 427 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 426
    simpa using h
  have hprev := st395o2_p426
  have hstep := st395o2_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p428 : ((193270998801/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 427, stT395o2 (i+1)) + stT395o2 428 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 427
    simpa using h
  have hprev := st395o2_p427
  have hstep := st395o2_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p429 : ((1475294051067/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 428, stT395o2 (i+1)) + stT395o2 429 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 428
    simpa using h
  have hprev := st395o2_p428
  have hstep := st395o2_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p430 : ((1440929414887/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 429, stT395o2 (i+1)) + stT395o2 430 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 429
    simpa using h
  have hprev := st395o2_p429
  have hstep := st395o2_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p431 : ((906259384981/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 430, stT395o2 (i+1)) + stT395o2 431 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 430
    simpa using h
  have hprev := st395o2_p430
  have hstep := st395o2_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p432 : ((3751216901299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 431, stT395o2 (i+1)) + stT395o2 432 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 431
    simpa using h
  have hprev := st395o2_p431
  have hstep := st395o2_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p433 : ((7909081198449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 432, stT395o2 (i+1)) + stT395o2 433 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 432
    simpa using h
  have hprev := st395o2_p432
  have hstep := st395o2_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p434 : ((8386361072979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 433, stT395o2 (i+1)) + stT395o2 434 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 433
    simpa using h
  have hprev := st395o2_p433
  have hstep := st395o2_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p435 : ((2209256281971/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 434, stT395o2 (i+1)) + stT395o2 435 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 434
    simpa using h
  have hprev := st395o2_p434
  have hstep := st395o2_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p436 : ((9170075116561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 435, stT395o2 (i+1)) + stT395o2 436 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 435
    simpa using h
  have hprev := st395o2_p435
  have hstep := st395o2_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p437 : ((9318999397041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 436, stT395o2 (i+1)) + stT395o2 437 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 436
    simpa using h
  have hprev := st395o2_p436
  have hstep := st395o2_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p438 : ((1850950944243/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 437, stT395o2 (i+1)) + stT395o2 438 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 437
    simpa using h
  have hprev := st395o2_p437
  have hstep := st395o2_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p439 : ((1798219326353/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 438, stT395o2 (i+1)) + stT395o2 439 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 438
    simpa using h
  have hprev := st395o2_p438
  have hstep := st395o2_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p440 : ((8581250608097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 439, stT395o2 (i+1)) + stT395o2 440 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 439
    simpa using h
  have hprev := st395o2_p439
  have hstep := st395o2_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p441 : ((324274917737/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 440, stT395o2 (i+1)) + stT395o2 441 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 440
    simpa using h
  have hprev := st395o2_p440
  have hstep := st395o2_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p442 : ((7661598934057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 441, stT395o2 (i+1)) + stT395o2 442 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 441
    simpa using h
  have hprev := st395o2_p441
  have hstep := st395o2_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p443 : ((7332540936667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 442, stT395o2 (i+1)) + stT395o2 443 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 442
    simpa using h
  have hprev := st395o2_p442
  have hstep := st395o2_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p444 : ((1436675392067/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 443, stT395o2 (i+1)) + stT395o2 444 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 443
    simpa using h
  have hprev := st395o2_p443
  have hstep := st395o2_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p445 : ((1448457116879/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 444, stT395o2 (i+1)) + stT395o2 445 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 444
    simpa using h
  have hprev := st395o2_p444
  have hstep := st395o2_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p446 : ((3748487247609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 445, stT395o2 (i+1)) + stT395o2 446 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 445
    simpa using h
  have hprev := st395o2_p445
  have hstep := st395o2_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p447 : ((3948780412653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 446, stT395o2 (i+1)) + stT395o2 447 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 446
    simpa using h
  have hprev := st395o2_p446
  have hstep := st395o2_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p448 : ((4183321248303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 447, stT395o2 (i+1)) + stT395o2 448 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 447
    simpa using h
  have hprev := st395o2_p447
  have hstep := st395o2_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p449 : ((1101801681387/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 448, stT395o2 (i+1)) + stT395o2 449 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 448
    simpa using h
  have hprev := st395o2_p448
  have hstep := st395o2_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p450 : ((1144486842183/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 449, stT395o2 (i+1)) + stT395o2 450 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 449
    simpa using h
  have hprev := st395o2_p449
  have hstep := st395o2_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p451 : ((9326945556881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 450, stT395o2 (i+1)) + stT395o2 451 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 450
    simpa using h
  have hprev := st395o2_p450
  have hstep := st395o2_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p452 : ((929608470131/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 451, stT395o2 (i+1)) + stT395o2 452 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 451
    simpa using h
  have hprev := st395o2_p451
  have hstep := st395o2_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p453 : ((9069948818487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 452, stT395o2 (i+1)) + stT395o2 453 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 452
    simpa using h
  have hprev := st395o2_p452
  have hstep := st395o2_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p454 : ((1738318496287/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 453, stT395o2 (i+1)) + stT395o2 454 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 453
    simpa using h
  have hprev := st395o2_p453
  have hstep := st395o2_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p455 : ((8231982025587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 454, stT395o2 (i+1)) + stT395o2 455 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 454
    simpa using h
  have hprev := st395o2_p454
  have hstep := st395o2_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p456 : ((7776528683061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 455, stT395o2 (i+1)) + stT395o2 456 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 455
    simpa using h
  have hprev := st395o2_p455
  have hstep := st395o2_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p457 : ((740913769569/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 456, stT395o2 (i+1)) + stT395o2 457 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 456
    simpa using h
  have hprev := st395o2_p456
  have hstep := st395o2_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p458 : ((89960600707/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 457, stT395o2 (i+1)) + stT395o2 458 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 457
    simpa using h
  have hprev := st395o2_p457
  have hstep := st395o2_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p459 : ((7177793472257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 458, stT395o2 (i+1)) + stT395o2 459 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 458
    simpa using h
  have hprev := st395o2_p458
  have hstep := st395o2_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p460 : ((7354608819461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 459, stT395o2 (i+1)) + stT395o2 460 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 459
    simpa using h
  have hprev := st395o2_p459
  have hstep := st395o2_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p461 : ((7694447840297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 460, stT395o2 (i+1)) + stT395o2 461 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 460
    simpa using h
  have hprev := st395o2_p460
  have hstep := st395o2_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p462 : ((8135319068611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 461, stT395o2 (i+1)) + stT395o2 462 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 461
    simpa using h
  have hprev := st395o2_p461
  have hstep := st395o2_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p463 : ((8597615400427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 462, stT395o2 (i+1)) + stT395o2 463 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 462
    simpa using h
  have hprev := st395o2_p462
  have hstep := st395o2_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p464 : ((8998563369649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 463, stT395o2 (i+1)) + stT395o2 464 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 463
    simpa using h
  have hprev := st395o2_p463
  have hstep := st395o2_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p465 : ((9267007849447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 464, stT395o2 (i+1)) + stT395o2 465 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 464
    simpa using h
  have hprev := st395o2_p464
  have hstep := st395o2_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p466 : ((4677948887607/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 465, stT395o2 (i+1)) + stT395o2 466 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 465
    simpa using h
  have hprev := st395o2_p465
  have hstep := st395o2_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p467 : ((9250277617199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 466, stT395o2 (i+1)) + stT395o2 467 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 466
    simpa using h
  have hprev := st395o2_p466
  have hstep := st395o2_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p468 : ((8969522076333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 467, stT395o2 (i+1)) + stT395o2 468 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 467
    simpa using h
  have hprev := st395o2_p467
  have hstep := st395o2_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p469 : ((8563507963851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 468, stT395o2 (i+1)) + stT395o2 469 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 468
    simpa using h
  have hprev := st395o2_p468
  have hstep := st395o2_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p470 : ((1620709377073/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 469, stT395o2 (i+1)) + stT395o2 470 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 469
    simpa using h
  have hprev := st395o2_p469
  have hstep := st395o2_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p471 : ((7669722595157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 470, stT395o2 (i+1)) + stT395o2 471 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 470
    simpa using h
  have hprev := st395o2_p470
  have hstep := st395o2_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p472 : ((7336938053461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 471, stT395o2 (i+1)) + stT395o2 472 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 471
    simpa using h
  have hprev := st395o2_p471
  have hstep := st395o2_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p473 : ((1432415514473/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 472, stT395o2 (i+1)) + stT395o2 473 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 472
    simpa using h
  have hprev := st395o2_p472
  have hstep := st395o2_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p474 : ((57395847317/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 473, stT395o2 (i+1)) + stT395o2 474 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 473
    simpa using h
  have hprev := st395o2_p473
  have hstep := st395o2_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p475 : ((3685628276889/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 474, stT395o2 (i+1)) + stT395o2 475 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 474
    simpa using h
  have hprev := st395o2_p474
  have hstep := st395o2_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p476 : ((7718180453529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 475, stT395o2 (i+1)) + stT395o2 476 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 475
    simpa using h
  have hprev := st395o2_p475
  have hstep := st395o2_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p477 : ((8155886694017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 476, stT395o2 (i+1)) + stT395o2 477 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 476
    simpa using h
  have hprev := st395o2_p476
  have hstep := st395o2_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p478 : ((861018237221/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 477, stT395o2 (i+1)) + stT395o2 478 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 477
    simpa using h
  have hprev := st395o2_p477
  have hstep := st395o2_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p479 : ((450234651847/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 478, stT395o2 (i+1)) + stT395o2 479 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 478
    simpa using h
  have hprev := st395o2_p478
  have hstep := st395o2_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p480 : ((927365831513/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 479, stT395o2 (i+1)) + stT395o2 480 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 479
    simpa using h
  have hprev := st395o2_p479
  have hstep := st395o2_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p481 : ((937278584297/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 480, stT395o2 (i+1)) + stT395o2 481 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 480
    simpa using h
  have hprev := st395o2_p480
  have hstep := st395o2_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p482 : ((4643150257229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 481, stT395o2 (i+1)) + stT395o2 482 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 481
    simpa using h
  have hprev := st395o2_p481
  have hstep := st395o2_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p483 : ((4514621660201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 482, stT395o2 (i+1)) + stT395o2 483 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 482
    simpa using h
  have hprev := st395o2_p482
  have hstep := st395o2_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p484 : ((4322294611227/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 483, stT395o2 (i+1)) + stT395o2 484 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 483
    simpa using h
  have hprev := st395o2_p483
  have hstep := st395o2_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p485 : ((4097945155221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 484, stT395o2 (i+1)) + stT395o2 485 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 484
    simpa using h
  have hprev := st395o2_p484
  have hstep := st395o2_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p486 : ((3878316265421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 485, stT395o2 (i+1)) + stT395o2 486 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 485
    simpa using h
  have hprev := st395o2_p485
  have hstep := st395o2_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p487 : ((3699090789689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 486, stT395o2 (i+1)) + stT395o2 487 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 486
    simpa using h
  have hprev := st395o2_p486
  have hstep := st395o2_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p488 : ((1794561871807/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 487, stT395o2 (i+1)) + stT395o2 488 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 487
    simpa using h
  have hprev := st395o2_p487
  have hstep := st395o2_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p489 : ((1782932685151/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 488, stT395o2 (i+1)) + stT395o2 489 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 488
    simpa using h
  have hprev := st395o2_p488
  have hstep := st395o2_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p490 : ((3632708099441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 489, stT395o2 (i+1)) + stT395o2 490 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 489
    simpa using h
  have hprev := st395o2_p489
  have hstep := st395o2_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p491 : ((94465086359/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 490, stT395o2 (i+1)) + stT395o2 491 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 490
    simpa using h
  have hprev := st395o2_p490
  have hstep := st395o2_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p492 : ((1989995726497/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 491, stT395o2 (i+1)) + stT395o2 492 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 491
    simpa using h
  have hprev := st395o2_p491
  have hstep := st395o2_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p493 : ((4204695797719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 492, stT395o2 (i+1)) + stT395o2 493 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 492
    simpa using h
  have hprev := st395o2_p492
  have hstep := st395o2_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p494 : ((2208555125317/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 493, stT395o2 (i+1)) + stT395o2 494 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 493
    simpa using h
  have hprev := st395o2_p493
  have hstep := st395o2_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p495 : ((4583846180591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 494, stT395o2 (i+1)) + stT395o2 495 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 494
    simpa using h
  have hprev := st395o2_p494
  have hstep := st395o2_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p496 : ((935787451141/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 495, stT395o2 (i+1)) + stT395o2 496 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 495
    simpa using h
  have hprev := st395o2_p495
  have hstep := st395o2_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p497 : ((9375627210107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 496, stT395o2 (i+1)) + stT395o2 497 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 496
    simpa using h
  have hprev := st395o2_p496
  have hstep := st395o2_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p498 : ((4609432045433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 497, stT395o2 (i+1)) + stT395o2 498 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 497
    simpa using h
  have hprev := st395o2_p497
  have hstep := st395o2_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p499 : ((4456272997711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 498, stT395o2 (i+1)) + stT395o2 499 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 498
    simpa using h
  have hprev := st395o2_p498
  have hstep := st395o2_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_p500 : ((2126130227757/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT395o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT395o2 (i+1))
      = (∑ i ∈ Finset.range 499, stT395o2 (i+1)) + stT395o2 500 := by
    have h := Finset.sum_range_succ (fun i => stT395o2 (i+1)) 499
    simpa using h
  have hprev := st395o2_p499
  have hstep := st395o2_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st395o2_s500 :
    |Real.sin (((395 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))
      - ((16379/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log ((500 : ℕ)) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((500 : ℕ)) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact sinMulShift_eval (r := 1359857/2000000) (δ := 4951/500000000) (ψ := -555759/1000000) 395 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 395/2`** (evaluated boundary). -/
theorem station_395o2_sign : hardyG (((((395:ℕ)):ℝ)/2)) < 0 := by
  have hcore := phase_station_lower_half_eval 395 500 (by norm_num) (by norm_num)
    ((-555759/1000000 : ℚ) : ℝ)
  have hchain := st395o2_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT395o2 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((395 : ℕ) : ℝ) * (Real.log ((i+1 : ℕ)) / 2)
              - ((-555759/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st395o2_c500
  have hsinb := abs_le.mp st395o2_s500
  have hbdy_lo : ((-4495901150641/97516250000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((395 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ))) / 2
          - ((((395:ℕ)):ℝ)/2)
            * Real.sin (((395 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-555759/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((395:ℕ)):ℝ)/2) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((395:ℝ) * (Real.log (500:ℝ) / 2) - ((-555759/1000000 : ℚ) : ℝ))) / 2
        - ((395:ℝ)/2) * Real.sin ((395:ℝ) * (Real.log (500:ℝ) / 2) - ((-555759/1000000 : ℚ) : ℝ))
        ≥ ((-20106263/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((395:ℝ)/2) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-20106263/250000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-20106263/250000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-20106263/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((395:ℕ)):ℝ)/2)+1) * (((((395:ℕ)):ℝ)/2)+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((12736521226621/40000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((2126130227757/2500000000000 : ℚ) : ℝ) + ((-4495901150641/97516250000000 : ℚ) : ℝ)
      - ((12736521226621/40000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-555759/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line (((((395:ℕ)):ℝ)/2)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-555759/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((((395:ℕ)):ℝ)/2)))).re
      - Real.sin ((-555759/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((((395:ℕ)):ℝ)/2)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((((395:ℕ)):ℝ)/2))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((((395:ℕ)):ℝ)/2))
      = ((((((395:ℕ)):ℝ)/2)) * (Real.log (((((395:ℕ)):ℝ)/2)) - Real.log 2
          - Real.log Real.pi) - (((((395:ℕ)):ℝ)/2))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM : ((10571477/2000000 : ℚ) : ℝ) ≤ Real.log (((((395:ℕ)):ℝ)/2))
      ∧ Real.log (((((395:ℕ)):ℝ)/2)) ≤ ((52857387/10000000 : ℚ) : ℝ) := by
    have hsplit : Real.log (((((395:ℕ)):ℝ)/2))
        = Real.log ((((395:ℕ)):ℝ)) - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    have hM := log_br_395
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
  have hθwin : |(((-555759/1000000 : ℚ) : ℝ) + ((39:ℤ)) * (2*Real.pi) - Real.pi) - theta (((((395:ℕ)):ℝ)/2))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((((395:ℕ)):ℝ)/2)))
    (φ := ((-555759/1000000 : ℚ) : ℝ) + ((39:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-555759/1000000 : ℚ) : ℝ) + ((39:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-555759/1000000 : ℚ)) : ℝ) - Real.pi) + ((39:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-555759/1000000 : ℚ)) : ℝ) - Real.pi) 39).1,
    (cos_sin_shift ((((-555759/1000000 : ℚ)) : ℝ) - Real.pi) 39).2]
  exact cos_sin_flip ((-555759/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_395o2_sign
end AxiomAudit
