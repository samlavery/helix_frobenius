import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationHalfEval

/-!
# Station `t = 281/2` (rung-144.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

theorem log_br_281 :
    ((28191773/5000000 : ℚ) : ℝ) ≤ Real.log (281 : ℕ)
      ∧ Real.log (281 : ℕ) ≤ ((56383547/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT281o2 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((281 : ℕ) : ℝ) * (Real.log ((n : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))

theorem st281o2_c1 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((62499/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((0 : ℚ) : ℝ) ≤ Real.log ((1 : ℕ)) / 2 := by
    have h := (log_br_1).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((1 : ℕ)) / 2 ≤ ((0 : ℚ) : ℝ) := by
    have h := (log_br_1).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2829/2000000) (δ := 1/1000000000) (ψ := 2829/500000) 281 0
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t1 : ((499967/500000 : ℚ) : ℝ) ≤ stT281o2 1 := by
  have hc : ((499967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499967/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((499967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c2 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-999969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log ((2 : ℕ)) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((2 : ℕ)) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3917171/5000000) (δ := 3597/500000000) (ψ := 2829/500000) 281 15
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t2 : ((-1767800587573/2500000000000 : ℚ) : ℝ) ≤ stT281o2 2 := by
  have hc : ((-1000019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1767800587573/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-1000019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c3 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-916593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log ((3 : ℕ)) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((3 : ℕ)) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3412837/5000000) (δ := 221/31250000) (ψ := 2829/500000) 281 25
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t3 : ((-5292241110429/10000000000000 : ℚ) : ℝ) ≤ stT281o2 3 := by
  have hc : ((-916643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5292241110429/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-916643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c4 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((19999/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log ((4 : ℕ)) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((4 : ℕ)) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6279/2500000) (δ := 7079/1000000000) (ψ := 2829/500000) 281 31
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t4 : ((9999/20000 : ℚ) : ℝ) ≤ stT281o2 4 := by
  have hc : ((9999/10000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9999/20000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((9999/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c5 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((997241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log ((5 : ℕ)) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((5 : ℕ)) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -185743/10000000) (δ := 7143/1000000000) (ψ := 2829/500000) 281 36
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t5 : ((891914554557/2000000000000 : ℚ) : ℝ) ≤ stT281o2 5 := by
  have hc : ((997191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((891914554557/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((997191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c6 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((458733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log ((6 : ℕ)) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((6 : ℕ)) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1022831/10000000) (δ := 883/125000000) (ψ := 2829/500000) 281 40
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t6 : ((234083394157/625000000000 : ℚ) : ℝ) ≤ stT281o2 6 := by
  have hc : ((114677/125000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234083394157/625000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((114677/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c7 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-997101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log ((7 : ℕ)) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((7 : ℕ)) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7663589/10000000) (δ := 3593/500000000) (ψ := 2829/500000) 281 44
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t7 : ((-753775358279/2000000000000 : ℚ) : ℝ) ≤ stT281o2 7 := by
  have hc : ((-997151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-753775358279/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-997151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c8 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-39997/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log ((8 : ℕ)) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((8 : ℕ)) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7823389/10000000) (δ := 7071/1000000000) (ψ := 2829/500000) 281 46
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t8 : ((-70708912233/200000000000 : ℚ) : ℝ) ≤ stT281o2 8 := by
  have hc : ((-39999/40000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70708912233/200000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-39999/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c9 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((676121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log ((9 : ℕ)) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((9 : ℕ)) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1035389/5000000) (δ := 141/20000000) (ψ := 2829/500000) 281 49
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t9 : ((2253569774643/10000000000000 : ℚ) : ℝ) ≤ stT281o2 9 := by
  have hc : ((676071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2253569774643/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((676071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c10 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-39883/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log ((10 : ℕ)) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((10 : ℕ)) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7662727/10000000) (δ := 1417/200000000) (ψ := 2829/500000) 281 51
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t10 : ((-12612745803/40000000000 : ℚ) : ℝ) ≤ stT281o2 10 := by
  have hc : ((-7977/8000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12612745803/40000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-7977/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c11 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-732907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log ((11 : ℕ)) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((11 : ℕ)) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1196691/2000000) (δ := 883/125000000) (ψ := 2829/500000) 281 54
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t11 : ((-1104974456049/5000000000000 : ℚ) : ℝ) ≤ stT281o2 11 := by
  have hc : ((-732957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1104974456049/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-732957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c12 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-14349/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log ((12 : ℕ)) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((12 : ℕ)) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6836627/10000000) (δ := 111/15625000) (ψ := 2829/500000) 281 56
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t12 : ((-41424259723/156250000000 : ℚ) : ℝ) ≤ stT281o2 12 := by
  have hc : ((-459193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41424259723/156250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-459193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c13 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-122207/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log ((13 : ℕ)) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((13 : ℕ)) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 696301/1250000) (δ := 7061/1000000000) (ψ := 2829/500000) 281 57
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t13 : ((-338968971717/2000000000000 : ℚ) : ℝ) ≤ stT281o2 13 := by
  have hc : ((-122217/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-338968971717/2000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-122217/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c14 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((498633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log ((14 : ℕ)) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((14 : ℕ)) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 46229/2500000) (δ := 3589/500000000) (ψ := 2829/500000) 281 59
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t14 : ((20821651939/78125000000 : ℚ) : ℝ) ≤ stT281o2 14 := by
  have hc : ((31163/31250 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20821651939/78125000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((31163/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c15 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-470927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log ((15 : ℕ)) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((15 : ℕ)) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3498627/5000000) (δ := 7039/1000000000) (ψ := 2829/500000) 281 61
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t15 : ((-151999110441/625000000000 : ℚ) : ℝ) ≤ stT281o2 15 := by
  have hc : ((-58869/62500 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151999110441/625000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-58869/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c16 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((124987/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log ((16 : ℕ)) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((16 : ℕ)) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -36069/10000000) (δ := 7097/1000000000) (ψ := 2829/500000) 281 62
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t16 : ((499923/2000000 : ℚ) : ℝ) ≤ stT281o2 16 := by
  have hc : ((499923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499923/2000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((499923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c17 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-302333/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log ((17 : ℕ)) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((17 : ℕ)) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2775179/5000000) (δ := 7149/1000000000) (ψ := 2829/500000) 281 63
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t17 : ((-366663045903/2500000000000 : ℚ) : ℝ) ≤ stT281o2 17 := by
  have hc : ((-151179/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-366663045903/2500000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-151179/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c18 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-677733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log ((18 : ℕ)) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((18 : ℕ)) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -144717/250000) (δ := 3559/500000000) (ψ := 2829/500000) 281 65
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t18 : ((-1597550120009/10000000000000 : ℚ) : ℝ) ≤ stT281o2 18 := by
  have hc : ((-677783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1597550120009/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-677783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c19 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((538437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log ((19 : ℕ)) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((19 : ℕ)) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2505539/10000000) (δ := 289/40000000) (ψ := 2829/500000) 281 66
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t19 : ((1235144304759/10000000000000 : ℚ) : ℝ) ≤ stT281o2 19 := by
  have hc : ((538387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1235144304759/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((538387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c20 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((199381/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log ((20 : ℕ)) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((20 : ℕ)) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -196731/10000000) (δ := 7083/1000000000) (ψ := 2829/500000) 281 67
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t20 : ((445806913857/2000000000000 : ℚ) : ℝ) ≤ stT281o2 20 := by
  have hc : ((199371/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((445806913857/2000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((199371/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c21 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((55053/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log ((21 : ℕ)) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((21 : ℕ)) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1232863/10000000) (δ := 7163/1000000000) (ψ := 2829/500000) 281 68
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t21 : ((480514504511/2500000000000 : ℚ) : ℝ) ≤ stT281o2 21 := by
  have hc : ((440399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((480514504511/2500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((440399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c22 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((183599/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log ((22 : ℕ)) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((22 : ℕ)) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 37301/200000) (δ := 441/62500000) (ψ := 2829/500000) 281 69
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t22 : ((782815406211/5000000000000 : ℚ) : ℝ) ≤ stT281o2 22 := by
  have hc : ((367173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((782815406211/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((367173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c23 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((759461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log ((23 : ℕ)) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((23 : ℕ)) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 885391/5000000) (δ := 1801/250000000) (ψ := 2829/500000) 281 70
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t23 : ((197935161273/1250000000000 : ℚ) : ℝ) ≤ stT281o2 23 := by
  have hc : ((759411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197935161273/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((759411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c24 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((1149/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log ((24 : ℕ)) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((24 : ℕ)) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 505939/5000000) (δ := 7111/1000000000) (ψ := 2829/500000) 281 71
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t24 : ((37524133303/200000000000 : ℚ) : ℝ) ≤ stT281o2 24 := by
  have hc : ((18383/20000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37524133303/200000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((18383/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c25 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((989801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log ((25 : ℕ)) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((25 : ℕ)) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -178679/5000000) (δ := 1407/200000000) (ψ := 2829/500000) 281 72
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t25 : ((989751/5000000 : ℚ) : ℝ) ≤ stT281o2 25 := by
  have hc : ((989751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((989751/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((989751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c26 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((609299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log ((26 : ℕ)) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((26 : ℕ)) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -45781/200000) (δ := 897/125000000) (ψ := 2829/500000) 281 73
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t26 : ((1194835378089/10000000000000 : ℚ) : ℝ) ≤ stT281o2 26 := by
  have hc : ((609249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1194835378089/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((609249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c27 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-15989/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log ((27 : ℕ)) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((27 : ℕ)) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4740733/10000000) (δ := 7133/1000000000) (ψ := 2829/500000) 281 74
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t27 : ((-61551315483/1000000000000 : ℚ) : ℝ) ≤ stT281o2 27 := by
  have hc : ((-31983/100000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61551315483/1000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-31983/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c28 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-39897/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log ((28 : ℕ)) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((28 : ℕ)) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3837271/5000000) (δ := 7063/1000000000) (ψ := 2829/500000) 281 75
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t28 : ((-75402047877/400000000000 : ℚ) : ℝ) ≤ stT281o2 28 := by
  have hc : ((-39899/40000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75402047877/400000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-39899/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c29 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-285679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log ((29 : ℕ)) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((29 : ℕ)) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4651277/10000000) (δ := 7113/1000000000) (ψ := 2829/500000) 281 75
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t29 : ((-265292804733/5000000000000 : ℚ) : ℝ) ≤ stT281o2 29 := by
  have hc : ((-285729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265292804733/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-285729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c30 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((14728/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log ((30 : ℕ)) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((30 : ℕ)) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 53201/625000) (δ := 7097/1000000000) (ψ := 2829/500000) 281 76
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t30 : ((860418786811/5000000000000 : ℚ) : ℝ) ≤ stT281o2 30 := by
  have hc : ((471271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((860418786811/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((471271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c31 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((232919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log ((31 : ℕ)) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((31 : ℕ)) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -667859/2000000) (δ := 3527/500000000) (ψ := 2829/500000) 281 77
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t31 : ((418245066057/10000000000000 : ℚ) : ℝ) ≤ stT281o2 31 := by
  have hc : ((232869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((418245066057/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((232869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c32 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-499931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log ((32 : ℕ)) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((32 : ℕ)) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1953109/2500000) (δ := 111/15625000) (ψ := 2829/500000) 281 77
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t32 : ((-220951429563/1250000000000 : ℚ) : ℝ) ≤ stT281o2 32 := by
  have hc : ((-124989/125000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220951429563/1250000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-124989/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c33 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((49321/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log ((33 : ℕ)) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((33 : ℕ)) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2912997/10000000) (δ := 7041/1000000000) (ψ := 2829/500000) 281 78
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t33 : ((42922966623/625000000000 : ℚ) : ℝ) ≤ stT281o2 33 := by
  have hc : ((197259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42922966623/625000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((197259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c34 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((15073/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log ((34 : ℕ)) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((34 : ℕ)) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -23091/100000) (δ := 3517/500000000) (ψ := 2829/500000) 281 79
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t34 : ((20678260139/200000000000 : ℚ) : ℝ) ≤ stT281o2 34 := by
  have hc : ((60287/100000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20678260139/200000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((60287/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c35 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-249993/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log ((35 : ℕ)) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((35 : ℕ)) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1958801/2500000) (δ := 7077/1000000000) (ψ := 2829/500000) 281 80
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t35 : ((-845173093399/5000000000000 : ℚ) : ℝ) ≤ stT281o2 35 := by
  have hc : ((-500011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-845173093399/5000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-500011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c36 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((679343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log ((36 : ℕ)) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((36 : ℕ)) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 82393/400000) (δ := 3563/500000000) (ψ := 2829/500000) 281 80
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t36 : ((566077273569/5000000000000 : ℚ) : ℝ) ≤ stT281o2 36 := by
  have hc : ((679293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((566077273569/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((679293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c37 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-3889/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log ((37 : ℕ)) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((37 : ℕ)) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -50303/125000) (δ := 89/12500000) (ψ := 2829/500000) 281 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t37 : ((-320084853/50000000000 : ℚ) : ℝ) ≤ stT281o2 37 := by
  have hc : ((-1947/50000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-320084853/50000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-1947/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c38 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-536589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log ((38 : ℕ)) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((38 : ℕ)) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1068593/2000000) (δ := 361/50000000) (ψ := 2829/500000) 281 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t38 : ((-174108767077/2000000000000 : ℚ) : ℝ) ≤ stT281o2 38 := by
  have hc : ((-536639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174108767077/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-536639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c39 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((879283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log ((39 : ℕ)) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((39 : ℕ)) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1241103/10000000) (δ := 719/100000000) (ψ := 2829/500000) 281 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t39 : ((1407899097473/10000000000000 : ℚ) : ℝ) ≤ stT281o2 39 := by
  have hc : ((879233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1407899097473/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((879233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c40 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-996731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log ((40 : ℕ)) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((40 : ℕ)) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3825887/5000000) (δ := 709/100000000) (ψ := 2829/500000) 281 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t40 : ((-1576049313559/10000000000000 : ℚ) : ℝ) ≤ stT281o2 40 := by
  have hc : ((-996781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1576049313559/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-996781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c41 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((969691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log ((41 : ℕ)) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((41 : ℕ)) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 308543/5000000) (δ := 1789/250000000) (ψ := 2829/500000) 281 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t41 : ((1514324226417/10000000000000 : ℚ) : ℝ) ≤ stT281o2 41 := by
  have hc : ((969641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1514324226417/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((969641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c42 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-881883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log ((42 : ℕ)) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((42 : ℕ)) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1325319/2000000) (δ := 881/125000000) (ψ := 2829/500000) 281 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t42 : ((-680426302361/5000000000000 : ℚ) : ℝ) ≤ stT281o2 42 := by
  have hc : ((-881933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-680426302361/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-881933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c43 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((396403/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log ((43 : ℕ)) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((43 : ℕ)) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1638493/10000000) (δ := 3549/500000000) (ψ := 2829/500000) 281 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t43 : ((60447050433/500000000000 : ℚ) : ℝ) ≤ stT281o2 43 := by
  have hc : ((198189/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60447050433/500000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((198189/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c44 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-735881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log ((44 : ℕ)) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((44 : ℕ)) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -749301/1250000) (δ := 889/125000000) (ψ := 2829/500000) 281 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t44 : ((-1109457930567/10000000000000 : ℚ) : ℝ) ≤ stT281o2 44 := by
  have hc : ((-735931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1109457930567/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-735931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c45 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((725067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log ((45 : ℕ)) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((45 : ℕ)) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1899163/10000000) (δ := 889/125000000) (ψ := 2829/500000) 281 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t45 : ((1080790817087/10000000000000 : ℚ) : ℝ) ≤ stT281o2 45 := by
  have hc : ((725017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1080790817087/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((725017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c46 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-760893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log ((46 : ℕ)) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((46 : ℕ)) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -761089/1250000) (δ := 1771/250000000) (ψ := 2829/500000) 281 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t46 : ((-56097478903/500000000000 : ℚ) : ℝ) ≤ stT281o2 46 := by
  have hc : ((-760943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56097478903/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-760943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c47 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((208269/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log ((47 : ℕ)) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((47 : ℕ)) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 45793/312500) (δ := 3517/500000000) (ψ := 2829/500000) 281 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t47 : ((607546270937/5000000000000 : ℚ) : ℝ) ≤ stT281o2 47 := by
  have hc : ((416513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((607546270937/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((416513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c48 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-920061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log ((48 : ℕ)) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((48 : ℕ)) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -342379/500000) (δ := 3613/500000000) (ψ := 2829/500000) 281 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t48 : ((-83004133421/625000000000 : ℚ) : ℝ) ≤ stT281o2 48 := by
  have hc : ((-920111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83004133421/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-920111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c49 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((987549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log ((49 : ℕ)) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((49 : ℕ)) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 197457/5000000) (δ := 3613/500000000) (ψ := 2829/500000) 281 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t49 : ((1410712433929/10000000000000 : ℚ) : ℝ) ≤ stT281o2 49 := by
  have hc : ((987499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1410712433929/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((987499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c50 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-989487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log ((50 : ℕ)) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((50 : ℕ)) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7491147/10000000) (δ := 7027/1000000000) (ψ := 2829/500000) 281 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t50 : ((-699708539459/5000000000000 : ℚ) : ℝ) ≤ stT281o2 50 := by
  have hc : ((-989537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-699708539459/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-989537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c51 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((175087/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log ((51 : ℕ)) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((51 : ℕ)) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1261153/10000000) (δ := 7033/1000000000) (ψ := 2829/500000) 281 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t51 : ((6128920539/50000000000 : ℚ) : ℝ) ≤ stT281o2 51 := by
  have hc : ((175077/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6128920539/50000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((175077/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c52 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-607561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log ((52 : ℕ)) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((52 : ℕ)) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1111891/2000000) (δ := 7183/1000000000) (ψ := 2829/500000) 281 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t52 : ((-842605161861/10000000000000 : ℚ) : ℝ) ≤ stT281o2 52 := by
  have hc : ((-607611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-842605161861/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-607611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c53 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((93283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log ((53 : ℕ)) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((53 : ℕ)) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -864457/2500000) (δ := 719/100000000) (ψ := 2829/500000) 281 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t53 : ((12809965509/500000000000 : ℚ) : ℝ) ≤ stT281o2 53 := by
  have hc : ((46629/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12809965509/500000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((46629/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c54 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((160927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log ((54 : ℕ)) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((54 : ℕ)) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 776943/2500000) (δ := 357/50000000) (ψ := 2829/500000) 281 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t54 : ((109479892977/2500000000000 : ℚ) : ℝ) ≤ stT281o2 54 := by
  have hc : ((80451/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109479892977/2500000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((80451/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c55 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-388923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log ((55 : ℕ)) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((55 : ℕ)) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -615507/1000000) (δ := 3549/500000000) (ψ := 2829/500000) 281 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t55 : ((-327785927/3125000000 : ℚ) : ℝ) ≤ stT281o2 55 := by
  have hc : ((-97237/125000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-327785927/3125000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-97237/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c56 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((997581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log ((56 : ℕ)) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((56 : ℕ)) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 21741/1250000) (δ := 881/125000000) (ψ := 2829/500000) 281 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t56 : ((666503330243/5000000000000 : ℚ) : ℝ) ≤ stT281o2 56 := by
  have hc : ((997531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((666503330243/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((997531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c57 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-416793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log ((57 : ℕ)) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((57 : ℕ)) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 49929/78125) (δ := 1441/200000000) (ψ := 2829/500000) 281 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t57 : ((-276044597997/2500000000000 : ℚ) : ℝ) ≤ stT281o2 57 := by
  have hc : ((-208409/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-276044597997/2500000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-208409/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c58 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((283579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log ((58 : ℕ)) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((58 : ℕ)) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3208181/10000000) (δ := 1411/200000000) (ψ := 2829/500000) 281 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t58 : ((46536465357/1250000000000 : ℚ) : ℝ) ≤ stT281o2 58 := by
  have hc : ((283529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46536465357/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((283529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c59 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((5463/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log ((59 : ℕ)) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((59 : ℕ)) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2796227/10000000) (δ := 1411/200000000) (ψ := 2829/500000) 281 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t59 : ((56891247411/1000000000000 : ℚ) : ℝ) ≤ stT281o2 59 := by
  have hc : ((43699/100000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56891247411/1000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((43699/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c60 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-471661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log ((60 : ℕ)) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((60 : ℕ)) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3504121/5000000) (δ := 1803/250000000) (ψ := 2829/500000) 281 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t60 : ((-60894426757/500000000000 : ℚ) : ℝ) ≤ stT281o2 60 := by
  have hc : ((-235843/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60894426757/500000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-235843/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c61 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((177313/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log ((61 : ℕ)) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((61 : ℕ)) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -601163/5000000) (δ := 7091/1000000000) (ψ := 2829/500000) 281 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t61 : ((14188317969/125000000000 : ℚ) : ℝ) ≤ stT281o2 61 := by
  have hc : ((177303/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14188317969/125000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((177303/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c62 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-9231/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log ((62 : ℕ)) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((62 : ℕ)) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 180367/400000) (δ := 889/125000000) (ψ := 2829/500000) 281 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t62 : ((-5862964233/200000000000 : ℚ) : ℝ) ≤ stT281o2 62 := by
  have hc : ((-9233/40000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5862964233/200000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-9233/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c63 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-15341/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log ((63 : ℕ)) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((63 : ℕ)) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -697331/1250000) (δ := 3517/500000000) (ψ := 2829/500000) 281 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t63 : ((-38658849229/500000000000 : ℚ) : ℝ) ≤ stT281o2 63 := by
  have hc : ((-61369/100000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38658849229/500000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-61369/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c64 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((999823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log ((64 : ℕ)) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((64 : ℕ)) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -23529/5000000) (δ := 449/62500000) (ψ := 2829/500000) 281 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t64 : ((999773/8000000 : ℚ) : ℝ) ≤ stT281o2 64 := by
  have hc : ((999773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((999773/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((999773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c65 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-277649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log ((65 : ℕ)) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((65 : ℕ)) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5398793/10000000) (δ := 7169/1000000000) (ψ := 2829/500000) 281 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t65 : ((-43051548819/625000000000 : ℚ) : ℝ) ≤ stT281o2 65 := by
  have hc : ((-138837/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43051548819/625000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-138837/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c66 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-19829/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log ((66 : ℕ)) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((66 : ℕ)) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4946461/10000000) (δ := 3563/500000000) (ψ := 2829/500000) 281 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t66 : ((-9764356329/200000000000 : ℚ) : ℝ) ≤ stT281o2 66 := by
  have hc : ((-39663/100000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9764356329/200000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-39663/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c67 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((991003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log ((67 : ℕ)) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((67 : ℕ)) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 335601/10000000) (δ := 7077/1000000000) (ψ := 2829/500000) 281 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t67 : ((605320667191/5000000000000 : ℚ) : ℝ) ≤ stT281o2 67 := by
  have hc : ((990953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((605320667191/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((990953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c68 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-601171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log ((68 : ℕ)) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((68 : ℕ)) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1107881/2000000) (δ := 7027/1000000000) (ψ := 2829/500000) 281 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t68 : ((-729088081059/10000000000000 : ℚ) : ℝ) ≤ stT281o2 68 := by
  have hc : ((-601221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-729088081059/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-601221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c69 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-86181/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log ((69 : ℕ)) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((69 : ℕ)) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -504073/1000000) (δ := 7119/1000000000) (ψ := 2829/500000) 281 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t69 : ((-103761811069/2000000000000 : ℚ) : ℝ) ≤ stT281o2 69 := by
  have hc : ((-86191/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103761811069/2000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-86191/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c70 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((499993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log ((70 : ℕ)) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((70 : ℕ)) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 13301/10000000) (δ := 7069/1000000000) (ψ := 2829/500000) 281 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t70 : ((583570071/4882812500 : ℚ) : ℝ) ≤ stT281o2 70 := by
  have hc : ((15624/15625 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((583570071/4882812500 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((15624/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c71 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-414561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log ((71 : ℕ)) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((71 : ℕ)) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2497821/5000000) (δ := 1771/250000000) (ψ := 2829/500000) 281 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t71 : ((-246026435901/5000000000000 : ℚ) : ℝ) ≤ stT281o2 71 := by
  have hc : ((-414611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246026435901/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-414611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c72 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-680949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log ((72 : ℕ)) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((72 : ℕ)) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2899817/5000000) (δ := 1803/250000000) (ψ := 2829/500000) 281 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t72 : ((-50160343343/625000000000 : ℚ) : ℝ) ≤ stT281o2 72 := by
  have hc : ((-680999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50160343343/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-680999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c73 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((23199/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log ((73 : ℕ)) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((73 : ℕ)) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -954737/10000000) (δ := 3531/500000000) (ψ := 2829/500000) 281 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t73 : ((108603607101/1000000000000 : ℚ) : ℝ) ≤ stT281o2 73 := by
  have hc : ((92791/100000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108603607101/1000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((92791/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c74 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((41093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log ((74 : ℕ)) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((74 : ℕ)) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 382423/1000000) (δ := 3531/500000000) (ψ := 2829/500000) 281 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t74 : ((11927875617/2500000000000 : ℚ) : ℝ) ≤ stT281o2 74 := by
  have hc : ((41043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11927875617/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((41043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c75 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-240671/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log ((75 : ℕ)) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((75 : ℕ)) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7168869/10000000) (δ := 1787/250000000) (ψ := 2829/500000) 281 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t75 : ((-555834956267/5000000000000 : ℚ) : ℝ) ≤ stT281o2 75 := by
  have hc : ((-481367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-555834956267/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-481367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c76 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((534739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log ((76 : ℕ)) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((76 : ℕ)) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2516493/10000000) (δ := 1421/200000000) (ψ := 2829/500000) 281 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t76 : ((306664994371/5000000000000 : ℚ) : ℝ) ≤ stT281o2 76 := by
  have hc : ((534689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306664994371/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((534689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c77 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((168713/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log ((77 : ℕ)) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((77 : ℕ)) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1037541/5000000) (δ := 1431/200000000) (ψ := 2829/500000) 281 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t77 : ((76900773321/1000000000000 : ℚ) : ℝ) ≤ stT281o2 77 := by
  have hc : ((337401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76900773321/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((337401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c78 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-439119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log ((78 : ℕ)) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((78 : ℕ)) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3303701/5000000) (δ := 3599/500000000) (ψ := 2829/500000) 281 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t78 : ((-31077068127/312500000000 : ℚ) : ℝ) ≤ stT281o2 78 := by
  have hc : ((-54893/62500 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31077068127/312500000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-54893/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c79 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-27597/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log ((79 : ℕ)) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((79 : ℕ)) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1156497/2500000) (δ := 881/125000000) (ψ := 2829/500000) 281 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t79 : ((-485229359/15625000000 : ℚ) : ℝ) ≤ stT281o2 79 := by
  have hc : ((-13801/50000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-485229359/15625000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-13801/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c80 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((996551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log ((80 : ℕ)) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((80 : ℕ)) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -51921/2500000) (δ := 1441/200000000) (ψ := 2829/500000) 281 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t80 : ((1114121002533/10000000000000 : ℚ) : ℝ) ≤ stT281o2 80 := by
  have hc : ((996501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1114121002533/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((996501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c81 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-22841/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log ((81 : ℕ)) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((81 : ℕ)) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4155719/10000000) (δ := 1431/200000000) (ψ := 2829/500000) 281 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t81 : ((-6348199523/625000000000 : ℚ) : ℝ) ≤ stT281o2 81 := by
  have hc : ((-45707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6348199523/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-45707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c82 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-60639/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log ((82 : ℕ)) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((82 : ℕ)) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1810593/2500000) (δ := 7041/1000000000) (ψ := 2829/500000) 281 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t82 : ((-133936137823/1250000000000 : ℚ) : ℝ) ≤ stT281o2 82 := by
  have hc : ((-485137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133936137823/1250000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-485137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c83 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((92011/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log ((83 : ℕ)) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((83 : ℕ)) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -298473/1000000) (δ := 889/125000000) (ψ := 2829/500000) 281 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t83 : ((100981417537/2500000000000 : ℚ) : ℝ) ≤ stT281o2 83 := by
  have hc : ((183997/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100981417537/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((183997/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c84 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((882917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log ((84 : ℕ)) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((84 : ℕ)) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 305473/2500000) (δ := 14241/1000000000) (ψ := 2829/500000) 281 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t84 : ((963286472163/10000000000000 : ℚ) : ℝ) ≤ stT281o2 84 := by
  have hc : ((882867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((963286472163/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((882867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c85 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-54861/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log ((85 : ℕ)) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((85 : ℕ)) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5378743/10000000) (δ := 7041/1000000000) (ψ := 2829/500000) 281 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t85 : ((-29755285749/500000000000 : ℚ) : ℝ) ≤ stT281o2 85 := by
  have hc : ((-27433/50000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29755285749/500000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-27433/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c86 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-198537/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log ((86 : ℕ)) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((86 : ℕ)) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6221/10000) (δ := 7119/1000000000) (ψ := 2829/500000) 281 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t86 : ((-53525371309/625000000000 : ℚ) : ℝ) ≤ stT281o2 86 := by
  have hc : ((-397099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53525371309/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-397099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c87 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((64933/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log ((87 : ℕ)) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((87 : ℕ)) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1080117/5000000) (δ := 7069/1000000000) (ψ := 2829/500000) 281 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t87 : ((135957203/1953125000 : ℚ) : ℝ) ≤ stT281o2 87 := by
  have hc : ((2029/3125 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135957203/1953125000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((2029/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c88 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((737363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log ((88 : ℕ)) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((88 : ℕ)) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1854097/10000000) (δ := 7119/1000000000) (ψ := 2829/500000) 281 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t88 : ((785977869939/10000000000000 : ℚ) : ℝ) ≤ stT281o2 88 := by
  have hc : ((737313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((785977869939/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((737313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c89 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-687777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log ((89 : ℕ)) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((89 : ℕ)) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2911523/5000000) (δ := 1771/250000000) (ψ := 2829/500000) 281 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t89 : ((-364547622173/5000000000000 : ℚ) : ℝ) ≤ stT281o2 89 := by
  have hc : ((-687827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364547622173/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-687827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c90 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-363287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log ((90 : ℕ)) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((90 : ℕ)) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -745037/1250000) (δ := 3613/500000000) (ψ := 2829/500000) 281 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t90 : ((-23935289751/312500000000 : ℚ) : ℝ) ≤ stT281o2 90 := by
  have hc : ((-22707/31250 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23935289751/312500000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-22707/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c91 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((168421/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log ((91 : ℕ)) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((91 : ℕ)) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -519759/2500000) (δ := 443/31250000) (ψ := 2829/500000) 281 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t91 : ((88269968007/1250000000000 : ℚ) : ℝ) ≤ stT281o2 91 := by
  have hc : ((336817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88269968007/1250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((336817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c92 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((762313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log ((92 : ℕ)) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((92 : ℕ)) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1759793/10000000) (δ := 1769/250000000) (ψ := 2829/500000) 281 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t92 : ((198678515109/2500000000000 : ℚ) : ℝ) ≤ stT281o2 92 := by
  have hc : ((762263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198678515109/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((762263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c93 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-606819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log ((93 : ℕ)) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((93 : ℕ)) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2778561/5000000) (δ := 7127/1000000000) (ψ := 2829/500000) 281 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t93 : ((-78661752911/1250000000000 : ℚ) : ℝ) ≤ stT281o2 93 := by
  have hc : ((-606869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78661752911/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-606869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c94 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-417147/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log ((94 : ℕ)) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((94 : ℕ)) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6394117/10000000) (δ := 449/62500000) (ψ := 2829/500000) 281 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t94 : ((-53785047323/625000000000 : ℚ) : ℝ) ≤ stT281o2 94 := by
  have hc : ((-104293/125000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53785047323/625000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-104293/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c95 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((59921/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log ((95 : ℕ)) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((95 : ℕ)) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -535431/2000000) (δ := 7119/1000000000) (ψ := 2829/500000) 281 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t95 : ((122942430751/2500000000000 : ℚ) : ℝ) ≤ stT281o2 95 := by
  have hc : ((239659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122942430751/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((239659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c96 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((460461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log ((96 : ℕ)) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((96 : ℕ)) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1000889/10000000) (δ := 7169/1000000000) (ψ := 2829/500000) 281 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t96 : ((5874127379/62500000000 : ℚ) : ℝ) ≤ stT281o2 96 := by
  have hc : ((115109/125000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5874127379/62500000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((115109/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c97 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-281669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log ((97 : ℕ)) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((97 : ℕ)) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4640823/10000000) (δ := 1771/250000000) (ψ := 2829/500000) 281 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t97 : ((-286042541493/10000000000000 : ℚ) : ℝ) ≤ stT281o2 97 := by
  have hc : ((-281719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286042541493/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-281719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c98 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-246973/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log ((98 : ℕ)) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((98 : ℕ)) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1492909/2000000) (δ := 889/125000000) (ψ := 2829/500000) 281 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t98 : ((-498986287563/5000000000000 : ℚ) : ℝ) ≤ stT281o2 98 := by
  have hc : ((-493971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-498986287563/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-493971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c99 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((1139/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log ((99 : ℕ)) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((99 : ℕ)) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1949257/5000000) (δ := 7141/1000000000) (ψ := 2829/500000) 281 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t99 : ((569855979/500000000000 : ℚ) : ℝ) ≤ stT281o2 99 := by
  have hc : ((567/50000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((569855979/500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((567/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c100 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((197833/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log ((100 : ℕ)) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((100 : ℕ)) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -184173/5000000) (δ := 7191/1000000000) (ψ := 2829/500000) 281 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t100 : ((197822802177/2000000000000 : ℚ) : ℝ) ≤ stT281o2 100 := by
  have hc : ((197823/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197822802177/2000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((197823/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c101 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((62933/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log ((101 : ℕ)) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((101 : ℕ)) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 781683/2500000) (δ := 7191/1000000000) (ψ := 2829/500000) 281 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t101 : ((62610713151/2000000000000 : ℚ) : ℝ) ≤ stT281o2 101 := by
  have hc : ((62923/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62610713151/2000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((62923/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c102 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-437187/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log ((102 : ℕ)) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((102 : ℕ)) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 823419/1250000) (δ := 7041/1000000000) (ψ := 2829/500000) 281 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t102 : ((-27056536711/312500000000 : ℚ) : ℝ) ≤ stT281o2 102 := by
  have hc : ((-109303/125000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27056536711/312500000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-109303/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c103 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-32467/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log ((103 : ℕ)) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((103 : ℕ)) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5693781/10000000) (δ := 3549/500000000) (ψ := 2829/500000) 281 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t103 : ((-6398634487/100000000000 : ℚ) : ℝ) ≤ stT281o2 103 := by
  have hc : ((-64939/100000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6398634487/100000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-64939/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c104 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((37863/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log ((104 : ℕ)) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((104 : ℕ)) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2300039/10000000) (δ := 1421/200000000) (ψ := 2829/500000) 281 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t104 : ((14849854491/250000000000 : ℚ) : ℝ) ≤ stT281o2 104 := by
  have hc : ((302879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14849854491/250000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((302879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c105 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((182249/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log ((105 : ℕ)) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((105 : ℕ)) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 8291/78125) (δ := 1411/200000000) (ψ := 2829/500000) 281 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t105 : ((1778470401/20000000000 : ℚ) : ℝ) ≤ stT281o2 105 := by
  have hc : ((182239/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1778470401/20000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((182239/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c106 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-184399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log ((106 : ℕ)) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((106 : ℕ)) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4390641/10000000) (δ := 1441/200000000) (ψ := 2829/500000) 281 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t106 : ((-89576365707/5000000000000 : ℚ) : ℝ) ≤ stT281o2 106 := by
  have hc : ((-184449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89576365707/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-184449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c107 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-498909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log ((107 : ℕ)) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((107 : ℕ)) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7688809/10000000) (δ := 1787/250000000) (ψ := 2829/500000) 281 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t107 : ((-241168979179/2500000000000 : ℚ) : ℝ) ≤ stT281o2 107 := by
  have hc : ((-249467/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241168979179/2500000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-249467/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c108 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-40491/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log ((108 : ℕ)) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((108 : ℕ)) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4751687/10000000) (δ := 3599/500000000) (ψ := 2829/500000) 281 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t108 : ((-155874077239/5000000000000 : ℚ) : ℝ) ≤ stT281o2 108 := by
  have hc : ((-161989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155874077239/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-161989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c109 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((2569/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log ((109 : ℕ)) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((109 : ℕ)) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -378589/2500000) (δ := 3549/500000000) (ψ := 2829/500000) 281 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t109 : ((39368085339/500000000000 : ℚ) : ℝ) ≤ stT281o2 109 := by
  have hc : ((82203/100000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39368085339/500000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((82203/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c110 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((779221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log ((110 : ℕ)) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((110 : ℕ)) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 338687/2000000) (δ := 1421/200000000) (ψ := 2829/500000) 281 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t110 : ((371454970001/5000000000000 : ℚ) : ℝ) ≤ stT281o2 110 := by
  have hc : ((779171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((371454970001/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((779171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c111 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-73829/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log ((111 : ℕ)) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((111 : ℕ)) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1218053/2500000) (δ := 3549/500000000) (ψ := 2829/500000) 281 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t111 : ((-35042438781/1000000000000 : ℚ) : ℝ) ≤ stT281o2 111 := by
  have hc : ((-73839/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35042438781/1000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-73839/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c112 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-997731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log ((112 : ℕ)) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((112 : ℕ)) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -768553/1000000) (δ := 7163/1000000000) (ψ := 2829/500000) 281 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t112 : ((-58925952517/625000000000 : ℚ) : ℝ) ≤ stT281o2 112 := by
  have hc : ((-997781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58925952517/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-997781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c113 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-62943/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log ((113 : ℕ)) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((113 : ℕ)) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4563269/10000000) (δ := 7063/1000000000) (ψ := 2829/500000) 281 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t113 : ((-118447121831/5000000000000 : ℚ) : ℝ) ≤ stT281o2 113 := by
  have hc : ((-125911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118447121831/5000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-125911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c114 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((416187/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log ((114 : ℕ)) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((114 : ℕ)) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -734273/5000000) (δ := 709/100000000) (ψ := 2829/500000) 281 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t114 : ((38977108677/500000000000 : ℚ) : ℝ) ≤ stT281o2 114 := by
  have hc : ((208081/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38977108677/500000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((208081/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c115 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((160459/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log ((115 : ℕ)) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((115 : ℕ)) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 799583/5000000) (δ := 357/50000000) (ψ := 2829/500000) 281 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t115 : ((18702416787/250000000000 : ℚ) : ℝ) ≤ stT281o2 115 := by
  have hc : ((160449/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18702416787/250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((160449/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c116 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-35183/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log ((116 : ℕ)) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((116 : ℕ)) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4640289/10000000) (δ := 7113/1000000000) (ψ := 2829/500000) 281 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t116 : ((-130689637089/5000000000000 : ℚ) : ℝ) ≤ stT281o2 116 := by
  have hc : ((-140757/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130689637089/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-140757/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c117 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-199369/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log ((117 : ℕ)) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((117 : ℕ)) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7655349/10000000) (δ := 7213/1000000000) (ψ := 2829/500000) 281 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t117 : ((-184326084879/2000000000000 : ℚ) : ℝ) ≤ stT281o2 117 := by
  have hc : ((-199379/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184326084879/2000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-199379/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c118 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-43901/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log ((118 : ℕ)) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((118 : ℕ)) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5063231/10000000) (δ := 717/100000000) (ψ := 2829/500000) 281 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t118 : ((-808375319/20000000000 : ℚ) : ℝ) ≤ stT281o2 118 := by
  have hc : ((-21953/50000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-808375319/20000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-21953/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c119 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((66773/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log ((119 : ℕ)) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((119 : ℕ)) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2099103/10000000) (δ := 7083/1000000000) (ψ := 2829/500000) 281 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t119 : ((1912690377/31250000000 : ℚ) : ℝ) ≤ stT281o2 119 := by
  have hc : ((4173/6250 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1912690377/31250000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((4173/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c120 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((472023/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log ((120 : ℕ)) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((120 : ℕ)) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 840263/10000000) (δ := 361/50000000) (ψ := 2829/500000) 281 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t120 : ((21543640713/250000000000 : ℚ) : ℝ) ≤ stT281o2 120 := by
  have hc : ((235999/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21543640713/250000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((235999/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c121 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((4291/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log ((121 : ℕ)) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((121 : ℕ)) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 234701/625000) (δ := 7033/1000000000) (ψ := 2829/500000) 281 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t121 : ((3118451427/500000000000 : ℚ) : ℝ) ≤ stT281o2 121 := by
  have hc : ((34303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3118451427/500000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((34303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c122 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-885549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log ((122 : ℕ)) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((122 : ℕ)) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6646179/10000000) (δ := 7083/1000000000) (ψ := 2829/500000) 281 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t122 : ((-400892069721/5000000000000 : ℚ) : ℝ) ≤ stT281o2 122 := by
  have hc : ((-885599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400892069721/5000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-885599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c123 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-787643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log ((123 : ℕ)) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((123 : ℕ)) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -247777/400000) (δ := 7027/1000000000) (ψ := 2829/500000) 281 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t123 : ((-71023914731/1000000000000 : ℚ) : ℝ) ≤ stT281o2 123 := by
  have hc : ((-787693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71023914731/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-787693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c124 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((114321/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log ((124 : ℕ)) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((124 : ℕ)) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -837571/2500000) (δ := 3613/500000000) (ψ := 2829/500000) 281 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t124 : ((6415048731/312500000000 : ℚ) : ℝ) ≤ stT281o2 124 := by
  have hc : ((14287/62500 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6415048731/312500000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((14287/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c125 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((488849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log ((125 : ℕ)) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((125 : ℕ)) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -528973/10000000) (δ := 7127/1000000000) (ψ := 2829/500000) 281 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t125 : ((54652172981/625000000000 : ℚ) : ℝ) ≤ stT281o2 125 := by
  have hc : ((61103/62500 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54652172981/625000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((61103/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c126 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((615369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log ((126 : ℕ)) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((126 : ℕ)) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2269857/10000000) (δ := 7027/1000000000) (ψ := 2829/500000) 281 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t126 : ((54816923753/1000000000000 : ℚ) : ℝ) ≤ stT281o2 126 := by
  have hc : ((615319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54816923753/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((615319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c127 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-86599/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log ((127 : ℕ)) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((127 : ℕ)) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5046523/10000000) (δ := 897/125000000) (ψ := 2829/500000) 281 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t127 : ((-76853102413/2000000000000 : ℚ) : ℝ) ≤ stT281o2 127 := by
  have hc : ((-86609/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76853102413/2000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-86609/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c128 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-999779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log ((128 : ℕ)) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((128 : ℕ)) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7801447/10000000) (δ := 897/125000000) (ψ := 2829/500000) 281 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t128 : ((-220933213959/2500000000000 : ℚ) : ℝ) ≤ stT281o2 128 := by
  have hc : ((-999829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220933213959/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-999829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c129 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-47803/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log ((129 : ℕ)) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((129 : ℕ)) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2586509/5000000) (δ := 1771/250000000) (ψ := 2829/500000) 281 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t129 : ((-657696897/15625000000 : ℚ) : ℝ) ≤ stT281o2 129 := by
  have hc : ((-1494/3125 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-657696897/15625000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-1494/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c130 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((276737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log ((130 : ℕ)) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((130 : ℕ)) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1230333/5000000) (δ := 7169/1000000000) (ψ := 2829/500000) 281 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t130 : ((15168279581/312500000000 : ℚ) : ℝ) ≤ stT281o2 130 := by
  have hc : ((34589/62500 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15168279581/312500000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((34589/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c131 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((995737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log ((131 : ℕ)) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((131 : ℕ)) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 14433/625000) (δ := 3517/500000000) (ψ := 2829/500000) 281 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t131 : ((108741964331/1250000000000 : ℚ) : ℝ) ≤ stT281o2 131 := by
  have hc : ((995687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108741964331/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((995687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c132 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((39859/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log ((132 : ℕ)) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((132 : ℕ)) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 725511/2500000) (δ := 3567/500000000) (ψ := 2829/500000) 281 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t132 : ((4336055419/125000000000 : ℚ) : ℝ) ≤ stT281o2 132 := by
  have hc : ((19927/50000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4336055419/125000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((19927/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c133 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-605507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log ((133 : ℕ)) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((133 : ℕ)) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2776499/5000000) (δ := 3567/500000000) (ψ := 2829/500000) 281 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t133 : ((-52508453027/1000000000000 : ℚ) : ℝ) ≤ stT281o2 133 := by
  have hc : ((-605557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52508453027/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-605557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c134 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-198259/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log ((134 : ℕ)) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((134 : ℕ)) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -60191/80000) (δ := 7081/500000000) (ψ := 2829/500000) 281 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t134 : ((-171278442761/2000000000000 : ℚ) : ℝ) ≤ stT281o2 134 := by
  have hc : ((-198269/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171278442761/2000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-198269/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c135 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-384017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log ((135 : ℕ)) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((135 : ℕ)) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4912349/10000000) (δ := 1803/250000000) (ψ := 2829/500000) 281 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t135 : ((-330552256421/10000000000000 : ℚ) : ℝ) ≤ stT281o2 135 := by
  have hc : ((-384067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-330552256421/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-384067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c136 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((37463/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log ((136 : ℕ)) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((136 : ℕ)) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -290011/1250000) (δ := 7191/1000000000) (ψ := 2829/500000) 281 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t136 : ((64243086267/1250000000000 : ℚ) : ℝ) ≤ stT281o2 136 := by
  have hc : ((299679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64243086267/1250000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((299679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c137 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((7959/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log ((137 : ℕ)) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((137 : ℕ)) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 63301/2500000) (δ := 889/125000000) (ψ := 2829/500000) 281 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t137 : ((33997428101/400000000000 : ℚ) : ℝ) ≤ stT281o2 137 := by
  have hc : ((39793/40000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33997428101/400000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((39793/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c138 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((216447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log ((138 : ℕ)) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((138 : ℕ)) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 140387/500000) (δ := 3531/500000000) (ψ := 2829/500000) 281 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t138 : ((11514407877/312500000000 : ℚ) : ℝ) ≤ stT281o2 138 := by
  have hc : ((108211/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11514407877/312500000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((108211/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c139 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-268447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log ((139 : ℕ)) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((139 : ℕ)) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 534387/1000000) (δ := 1803/250000000) (ψ := 2829/500000) 281 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t139 : ((-28464374651/625000000000 : ℚ) : ℝ) ≤ stT281o2 139 := by
  have hc : ((-33559/62500 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28464374651/625000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-33559/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c140 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-199999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log ((140 : ℕ)) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((140 : ℕ)) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7846157/10000000) (δ := 3549/500000000) (ψ := 2829/500000) 281 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t140 : ((-33807721279/400000000000 : ℚ) : ℝ) ≤ stT281o2 140 := by
  have hc : ((-200009/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33807721279/400000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-200009/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c141 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-53767/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log ((141 : ℕ)) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((141 : ℕ)) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -534617/1000000) (δ := 3599/500000000) (ψ := 2829/500000) 281 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t141 : ((-1415131167/31250000000 : ℚ) : ℝ) ≤ stT281o2 141 := by
  have hc : ((-13443/25000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1415131167/31250000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-13443/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c142 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((412567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log ((142 : ℕ)) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((142 : ℕ)) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -357977/1250000) (δ := 3599/500000000) (ψ := 2829/500000) 281 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t142 : ((346176428577/10000000000000 : ℚ) : ℝ) ≤ stT281o2 142 := by
  have hc : ((412517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((346176428577/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((412517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c143 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((493649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log ((143 : ℕ)) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((143 : ℕ)) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -99721/2500000) (δ := 3599/500000000) (ψ := 2829/500000) 281 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t143 : ((25799320063/312500000000 : ℚ) : ℝ) ≤ stT281o2 143 := by
  have hc : ((61703/62500 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25799320063/312500000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((61703/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c144 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((341281/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log ((144 : ℕ)) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((144 : ℕ)) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 512209/2500000) (δ := 1431/200000000) (ψ := 2829/500000) 281 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t144 : ((35547485781/625000000000 : ℚ) : ℝ) ≤ stT281o2 144 := by
  have hc : ((42657/62500 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35547485781/625000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((42657/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c145 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-27409/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log ((145 : ℕ)) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((145 : ℕ)) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2239831/5000000) (δ := 881/125000000) (ψ := 2829/500000) 281 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t145 : ((-18213705151/1000000000000 : ℚ) : ℝ) ≤ stT281o2 145 := by
  have hc : ((-109661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18213705151/1000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-109661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c146 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-463571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log ((146 : ℕ)) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((146 : ℕ)) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 861721/1250000) (δ := 1411/200000000) (ψ := 2829/500000) 281 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t146 : ((-47959353897/625000000000 : ℚ) : ℝ) ≤ stT281o2 146 := by
  have hc : ((-115899/125000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47959353897/625000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-115899/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c147 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-419609/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log ((147 : ℕ)) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((147 : ℕ)) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3208299/5000000) (δ := 7097/1000000000) (ψ := 2829/500000) 281 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t147 : ((-173054333979/2500000000000 : ℚ) : ℝ) ≤ stT281o2 147 := by
  have hc : ((-209817/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173054333979/2500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-209817/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c148 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-43281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log ((148 : ℕ)) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((148 : ℕ)) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1008807/2500000) (δ := 3553/500000000) (ψ := 2829/500000) 281 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t148 : ((-7123573069/2000000000000 : ℚ) : ℝ) ≤ stT281o2 148 := by
  have hc : ((-43331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7123573069/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-43331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c149 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((785093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log ((149 : ℕ)) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((149 : ℕ)) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -417469/2500000) (δ := 7197/1000000000) (ψ := 2829/500000) 281 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t149 : ((643131561933/10000000000000 : ℚ) : ℝ) ≤ stT281o2 149 := by
  have hc : ((785043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((643131561933/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((785043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c150 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((481639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log ((150 : ℕ)) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((150 : ℕ)) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 679601/10000000) (δ := 3603/500000000) (ψ := 2829/500000) 281 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t150 : ((12288622017/156250000000 : ℚ) : ℝ) ≤ stT281o2 150 := by
  have hc : ((240807/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12288622017/156250000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((240807/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c151 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((178657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log ((151 : ℕ)) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((151 : ℕ)) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 753379/2500000) (δ := 7147/1000000000) (ψ := 2829/500000) 281 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t151 : ((4542768063/156250000000 : ℚ) : ℝ) ≤ stT281o2 151 := by
  have hc : ((22329/62500 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4542768063/156250000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((22329/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c152 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-532887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log ((152 : ℕ)) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((152 : ℕ)) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1333003/2500000) (δ := 7097/1000000000) (ψ := 2829/500000) 281 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t152 : ((-108067366049/2500000000000 : ℚ) : ℝ) ≤ stT281o2 152 := by
  have hc : ((-532937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108067366049/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-532937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c153 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-996177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log ((153 : ℕ)) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((153 : ℕ)) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7635299/10000000) (δ := 441/62500000) (ψ := 2829/500000) 281 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t153 : ((-805402706831/10000000000000 : ℚ) : ℝ) ≤ stT281o2 153 := by
  have hc : ((-996227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-805402706831/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-996227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c154 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-338233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log ((154 : ℕ)) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((154 : ℕ)) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -723047/1250000) (δ := 11/1562500) (ψ := 2829/500000) 281 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t154 : ((-136288038167/2500000000000 : ℚ) : ℝ) ≤ stT281o2 154 := by
  have hc : ((-169129/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136288038167/2500000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-169129/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c155 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((33133/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log ((155 : ℕ)) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((155 : ℕ)) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -351091/1000000) (δ := 7163/1000000000) (ψ := 2829/500000) 281 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t155 : ((26605022937/2000000000000 : ℚ) : ℝ) ≤ stT281o2 155 := by
  have hc : ((33123/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26605022937/2000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((33123/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c156 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((219297/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log ((156 : ℕ)) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((156 : ℕ)) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1252057/10000000) (δ := 357/50000000) (ψ := 2829/500000) 281 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t156 : ((548649819/7812500000 : ℚ) : ℝ) ≤ stT281o2 156 := by
  have hc : ((438569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((548649819/7812500000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((438569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c157 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((922247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log ((157 : ℕ)) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((157 : ℕ)) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 992361/10000000) (δ := 7213/1000000000) (ψ := 2829/500000) 281 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t157 : ((367996257471/5000000000000 : ℚ) : ℝ) ≤ stT281o2 157 := by
  have hc : ((922197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((367996257471/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((922197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c158 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((11123/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log ((158 : ℕ)) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((158 : ℕ)) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3222517/10000000) (δ := 11/1562500) (ψ := 2829/500000) 281 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t158 : ((8847389397/400000000000 : ℚ) : ℝ) ≤ stT281o2 158 := by
  have hc : ((11121/40000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8847389397/400000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((11121/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c159 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-568477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log ((159 : ℕ)) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((159 : ℕ)) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 169957/312500) (δ := 7213/1000000000) (ψ := 2829/500000) 281 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t159 : ((-112717868601/2500000000000 : ℚ) : ℝ) ≤ stT281o2 159 := by
  have hc : ((-568527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112717868601/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-568527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c160 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-996367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log ((160 : ℕ)) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((160 : ℕ)) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7640821/10000000) (δ := 7213/1000000000) (ψ := 2829/500000) 281 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t160 : ((-78773738769/1000000000000 : ℚ) : ℝ) ≤ stT281o2 160 := by
  have hc : ((-996417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78773738769/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-996417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c161 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-8797/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log ((161 : ℕ)) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((161 : ℕ)) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -146967/250000) (δ := 7183/1000000000) (ψ := 2829/500000) 281 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t161 : ((-55468040291/1000000000000 : ℚ) : ℝ) ≤ stT281o2 161 := by
  have hc : ((-70381/100000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55468040291/1000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-70381/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c162 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((44591/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log ((162 : ℕ)) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((162 : ℕ)) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -185187/500000) (δ := 7183/1000000000) (ψ := 2829/500000) 281 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t162 : ((8753586871/1250000000000 : ℚ) : ℝ) ≤ stT281o2 162 := by
  have hc : ((22283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8753586871/1250000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((22283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c163 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((815691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log ((163 : ℕ)) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((163 : ℕ)) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -771091/5000000) (δ := 89/12500000) (ψ := 2829/500000) 281 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t163 : ((31942948483/500000000000 : ℚ) : ℝ) ≤ stT281o2 163 := by
  have hc : ((815641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31942948483/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((815641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c164 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((15168/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log ((164 : ℕ)) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((164 : ℕ)) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 606133/10000000) (δ := 7033/1000000000) (ψ := 2829/500000) 281 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t164 : ((94748766167/1250000000000 : ℚ) : ℝ) ≤ stT281o2 164 := by
  have hc : ((485351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94748766167/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((485351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c165 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((228333/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log ((165 : ℕ)) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((165 : ℕ)) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1370691/5000000) (δ := 89/12500000) (ψ := 2829/500000) 281 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t165 : ((22217165173/625000000000 : ℚ) : ℝ) ≤ stT281o2 165 := by
  have hc : ((57077/125000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22217165173/625000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((57077/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c166 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-365993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log ((166 : ℕ)) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((166 : ℕ)) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 243187/500000) (δ := 717/100000000) (ψ := 2829/500000) 281 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t166 : ((-284104640493/10000000000000 : ℚ) : ℝ) ≤ stT281o2 166 := by
  have hc : ((-366043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284104640493/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-366043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c167 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-469301/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log ((167 : ℕ)) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((167 : ℕ)) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3486691/5000000) (δ := 7133/1000000000) (ψ := 2829/500000) 281 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t167 : ((-2837310333/39062500000 : ℚ) : ℝ) ≤ stT281o2 167 := by
  have hc : ((-234663/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2837310333/39062500000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-234663/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c168 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-883947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log ((168 : ℕ)) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((168 : ℕ)) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6637583/10000000) (δ := 7177/1000000000) (ψ := 2829/500000) 281 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t168 : ((-682018713449/10000000000000 : ℚ) : ℝ) ≤ stT281o2 168 := by
  have hc : ((-883997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-682018713449/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-883997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c169 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-247789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log ((169 : ℕ)) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((169 : ℕ)) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -910597/2000000) (δ := 1769/250000000) (ψ := 2829/500000) 281 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t169 : ((-190645441809/10000000000000 : ℚ) : ℝ) ≤ stT281o2 169 := by
  have hc : ((-247839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190645441809/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-247839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c170 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((546777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log ((170 : ℕ)) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((170 : ℕ)) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -496143/2000000) (δ := 7127/1000000000) (ψ := 2829/500000) 281 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t170 : ((104829981707/2500000000000 : ℚ) : ℝ) ≤ stT281o2 170 := by
  have hc : ((546727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104829981707/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((546727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c171 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((985881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log ((171 : ℕ)) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((171 : ℕ)) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -420599/10000000) (δ := 1769/250000000) (ψ := 2829/500000) 281 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t171 : ((753883696489/10000000000000 : ℚ) : ℝ) ≤ stT281o2 171 := by
  have hc : ((985831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((753883696489/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((985831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c172 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((795477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log ((172 : ℕ)) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((172 : ℕ)) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 325501/2000000) (δ := 7127/1000000000) (ψ := 2829/500000) 281 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t172 : ((151626681021/2500000000000 : ℚ) : ℝ) ≤ stT281o2 172 := by
  have hc : ((795427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151626681021/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((795427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c173 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((105107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log ((173 : ℕ)) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((173 : ℕ)) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 457967/1250000) (δ := 1769/250000000) (ψ := 2829/500000) 281 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t173 : ((15974652249/2000000000000 : ℚ) : ℝ) ≤ stT281o2 173 := by
  have hc : ((105057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15974652249/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((105057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c174 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-647651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log ((174 : ℕ)) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((174 : ℕ)) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1422059/2500000) (δ := 7127/1000000000) (ψ := 2829/500000) 281 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t174 : ((-491021480399/10000000000000 : ℚ) : ℝ) ≤ stT281o2 174 := by
  have hc : ((-647701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-491021480399/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-647701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c175 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-249533/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log ((175 : ℕ)) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((175 : ℕ)) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 962643/1250000) (δ := 1769/250000000) (ψ := 2829/500000) 281 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t175 : ((-377277360539/5000000000000 : ℚ) : ℝ) ≤ stT281o2 175 := by
  have hc : ((-499091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-377277360539/5000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-499091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c176 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-14777/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log ((176 : ℕ)) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((176 : ℕ)) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6005397/10000000) (δ := 7169/1000000000) (ψ := 2829/500000) 281 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t176 : ((-5569673031/100000000000 : ℚ) : ℝ) ≤ stT281o2 176 := by
  have hc : ((-7389/10000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5569673031/100000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-7389/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c177 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-3531/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log ((177 : ℕ)) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((177 : ℕ)) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1003821/2500000) (δ := 449/62500000) (ψ := 2829/500000) 281 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t177 : ((-166113987/62500000000 : ℚ) : ℝ) ≤ stT281o2 177 := by
  have hc : ((-221/6250 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166113987/62500000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-221/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c178 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((137237/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log ((178 : ℕ)) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((178 : ℕ)) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -509103/2500000) (δ := 1771/250000000) (ψ := 2829/500000) 281 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t178 : ((102855890537/2000000000000 : ℚ) : ℝ) ≤ stT281o2 178 := by
  have hc : ((137227/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102855890537/2000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((137227/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c179 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((124953/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log ((179 : ℕ)) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((179 : ℕ)) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -17151/2500000) (δ := 3567/500000000) (ψ := 2829/500000) 281 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t179 : ((74711659269/1000000000000 : ℚ) : ℝ) ≤ stT281o2 179 := by
  have hc : ((499787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74711659269/1000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((499787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c180 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((728077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log ((180 : ℕ)) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((180 : ℕ)) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1888209/10000000) (δ := 7219/1000000000) (ψ := 2829/500000) 281 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t180 : ((108527712917/2000000000000 : ℚ) : ℝ) ≤ stT281o2 180 := by
  have hc : ((728027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108527712917/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((728027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c181 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((18553/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log ((181 : ℕ)) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((181 : ℕ)) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 766841/2000000) (δ := 3567/500000000) (ψ := 2829/500000) 281 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t181 : ((215183613/78125000000 : ℚ) : ℝ) ≤ stT281o2 181 := by
  have hc : ((579/15625 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215183613/78125000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((579/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c182 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-336029/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log ((182 : ℕ)) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((182 : ℕ)) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1442363/2500000) (δ := 3567/500000000) (ψ := 2829/500000) 281 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t182 : ((-99640011/2000000000 : ℚ) : ℝ) ≤ stT281o2 182 := by
  have hc : ((-168027/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99640011/2000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-168027/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c183 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-249489/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log ((183 : ℕ)) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((183 : ℕ)) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3847063/5000000) (δ := 7069/1000000000) (ψ := 2829/500000) 281 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t183 : ((-184436997833/2500000000000 : ℚ) : ℝ) ≤ stT281o2 183 := by
  have hc : ((-499003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184436997833/2500000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-499003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c184 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-763729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log ((184 : ℕ)) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((184 : ℕ)) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1219933/2000000) (δ := 1773/250000000) (ψ := 2829/500000) 281 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t184 : ((-56306551659/1000000000000 : ℚ) : ℝ) ≤ stT281o2 184 := by
  have hc : ((-763779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56306551659/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-763779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c185 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-53669/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log ((185 : ℕ)) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((185 : ℕ)) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -839171/2000000) (δ := 3521/500000000) (ψ := 2829/500000) 281 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t185 : ((-3947663421/500000000000 : ℚ) : ℝ) ≤ stT281o2 185 := by
  have hc : ((-26847/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3947663421/500000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-26847/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c186 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((151269/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log ((186 : ℕ)) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((186 : ℕ)) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2302337/10000000) (δ := 7211/1000000000) (ψ := 2829/500000) 281 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t186 : ((44362623911/1000000000000 : ℚ) : ℝ) ≤ stT281o2 186 := by
  have hc : ((302513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44362623911/1000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((302513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c187 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((123249/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log ((187 : ℕ)) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((187 : ℕ)) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -209467/5000000) (δ := 3521/500000000) (ψ := 2829/500000) 281 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t187 : ((45061986139/625000000000 : ℚ) : ℝ) ≤ stT281o2 187 := by
  have hc : ((492971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45061986139/625000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((492971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c188 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((835499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log ((188 : ℕ)) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((188 : ℕ)) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 363597/2500000) (δ := 899/125000000) (ψ := 2829/500000) 281 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t188 : ((152328251619/2500000000000 : ℚ) : ℝ) ≤ stT281o2 188 := by
  have hc : ((835449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152328251619/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((835449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c189 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((24127/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log ((189 : ℕ)) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((189 : ℕ)) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 829451/2500000) (δ := 3521/500000000) (ψ := 2829/500000) 281 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t189 : ((274158591/15625000000 : ℚ) : ℝ) ≤ stT281o2 189 := by
  have hc : ((12061/50000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274158591/15625000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((12061/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c190 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-119361/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log ((190 : ℕ)) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((190 : ℕ)) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 103427/200000) (δ := 7111/1000000000) (ψ := 2829/500000) 281 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t190 : ((-173205457319/5000000000000 : ℚ) : ℝ) ≤ stT281o2 190 := by
  have hc : ((-238747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173205457319/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-238747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c191 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-472121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log ((191 : ℕ)) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((191 : ℕ)) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3507601/5000000) (δ := 3521/500000000) (ψ := 2829/500000) 281 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t191 : ((-6832660839/100000000000 : ℚ) : ℝ) ≤ stT281o2 191 := by
  have hc : ((-236073/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6832660839/100000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-236073/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c192 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-460887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log ((192 : ℕ)) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((192 : ℕ)) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6858569/10000000) (δ := 3527/500000000) (ψ := 2829/500000) 281 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t192 : ((-2598708277/39062500000 : ℚ) : ℝ) ≤ stT281o2 192 := by
  have hc : ((-28807/31250 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2598708277/39062500000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-28807/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c193 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-107109/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log ((193 : ℕ)) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((193 : ℕ)) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1006779/2000000) (δ := 7199/1000000000) (ψ := 2829/500000) 281 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t193 : ((-19276942411/625000000000 : ℚ) : ℝ) ≤ stT281o2 193 := by
  have hc : ((-214243/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19276942411/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-214243/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c194 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((139783/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log ((194 : ℕ)) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((194 : ℕ)) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -643727/2000000) (δ := 7199/1000000000) (ψ := 2829/500000) 281 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t194 : ((25085093541/1250000000000 : ℚ) : ℝ) ≤ stT281o2 194 := by
  have hc : ((69879/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25085093541/1250000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((69879/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c195 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((422271/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log ((195 : ℕ)) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((195 : ℕ)) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1412719/10000000) (δ := 3577/500000000) (ψ := 2829/500000) 281 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t195 : ((75594068011/1250000000000 : ℚ) : ℝ) ≤ stT281o2 195 := by
  have hc : ((211123/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75594068011/1250000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((211123/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c196 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((988229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log ((196 : ℕ)) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((196 : ℕ)) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 9599/250000) (δ := 111/15625000) (ψ := 2829/500000) 281 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t196 : ((141168287403/2000000000000 : ℚ) : ℝ) ≤ stT281o2 196 := by
  have hc : ((988179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141168287403/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((988179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c197 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((322947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log ((197 : ℕ)) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((197 : ℕ)) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2171507/10000000) (δ := 7199/1000000000) (ψ := 2829/500000) 281 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t197 : ((11503611867/250000000000 : ℚ) : ℝ) ≤ stT281o2 197 := by
  have hc : ((161461/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11503611867/250000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((161461/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c198 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-23/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log ((198 : ℕ)) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((198 : ℕ)) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3949991/10000000) (δ := 7149/1000000000) (ψ := 2829/500000) 281 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t198 : ((-2629479/4000000000 : ℚ) : ℝ) ≤ stT281o2 198 := by
  have hc : ((-37/4000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2629479/4000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-37/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c199 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-328567/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log ((199 : ℕ)) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((199 : ℕ)) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2859759/5000000) (δ := 7049/1000000000) (ψ := 2829/500000) 281 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t199 : ((-7279154817/156250000000 : ℚ) : ℝ) ≤ stT281o2 199 := by
  have hc : ((-20537/31250 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7279154817/156250000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-20537/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c200 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-988841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log ((200 : ℕ)) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((200 : ℕ)) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7480159/10000000) (δ := 7199/1000000000) (ψ := 2829/500000) 281 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t200 : ((-699251748337/10000000000000 : ℚ) : ℝ) ≤ stT281o2 200 := by
  have hc : ((-988891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-699251748337/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-988891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c201 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-425941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log ((201 : ℕ)) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((201 : ℕ)) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -647591/1000000) (δ := 3553/500000000) (ψ := 2829/500000) 281 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t201 : ((-75113353559/1250000000000 : ℚ) : ℝ) ≤ stT281o2 201 := by
  have hc : ((-212983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75113353559/1250000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-212983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c202 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-316757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log ((202 : ℕ)) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((202 : ℕ)) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2366381/5000000) (δ := 7097/1000000000) (ψ := 2829/500000) 281 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t202 : ((-111452385793/5000000000000 : ℚ) : ℝ) ≤ stT281o2 202 := by
  have hc : ((-316807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111452385793/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-316807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c203 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((72607/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log ((203 : ℕ)) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((203 : ℕ)) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -374773/1250000) (δ := 7047/1000000000) (ψ := 2829/500000) 281 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t203 : ((25476537807/1000000000000 : ℚ) : ℝ) ≤ stT281o2 203 := by
  have hc : ((72597/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25476537807/1000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((72597/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c204 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((436651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log ((204 : ℕ)) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((204 : ℕ)) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1272141/10000000) (δ := 3603/500000000) (ψ := 2829/500000) 281 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t204 : ((7642483191/125000000000 : ℚ) : ℝ) ≤ stT281o2 204 := by
  have hc : ((218313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7642483191/125000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((218313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c205 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((492083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log ((205 : ℕ)) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((205 : ℕ)) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 445471/10000000) (δ := 7047/1000000000) (ψ := 2829/500000) 281 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t205 : ((17183403447/250000000000 : ℚ) : ℝ) ≤ stT281o2 205 := by
  have hc : ((246029/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17183403447/250000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((246029/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c206 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((162751/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log ((206 : ℕ)) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((206 : ℕ)) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 538681/2500000) (δ := 3553/500000000) (ψ := 2829/500000) 281 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t206 : ((226770566641/5000000000000 : ℚ) : ℝ) ≤ stT281o2 206 := by
  have hc : ((325477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226770566641/5000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((325477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c207 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((14259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log ((207 : ℕ)) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((207 : ℕ)) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3855687/10000000) (δ := 7047/1000000000) (ψ := 2829/500000) 281 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t207 : ((618332077/312500000000 : ℚ) : ℝ) ≤ stT281o2 207 := by
  have hc : ((7117/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((618332077/312500000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((7117/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c208 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-604063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log ((208 : ℕ)) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((208 : ℕ)) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2774233/5000000) (δ := 7097/1000000000) (ψ := 2829/500000) 281 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t208 : ((-3272480121/78125000000 : ℚ) : ℝ) ≤ stT281o2 208 := by
  have hc : ((-604113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3272480121/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-604113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c209 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-484661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log ((209 : ℕ)) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((209 : ℕ)) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7233131/10000000) (δ := 7197/1000000000) (ψ := 2829/500000) 281 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t209 : ((-33526457649/500000000000 : ℚ) : ℝ) ≤ stT281o2 209 := by
  have hc : ((-242343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33526457649/500000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-242343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c210 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-182429/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log ((210 : ℕ)) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((210 : ℕ)) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -679821/1000000) (δ := 7113/1000000000) (ψ := 2829/500000) 281 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t210 : ((-62947475487/1000000000000 : ℚ) : ℝ) ≤ stT281o2 210 := by
  have hc : ((-182439/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62947475487/1000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-182439/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c211 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-462691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log ((211 : ℕ)) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((211 : ℕ)) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2564781/5000000) (δ := 11/1562500) (ψ := 2829/500000) 281 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t211 : ((-318564323889/10000000000000 : ℚ) : ℝ) ≤ stT281o2 211 := by
  have hc : ((-462741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-318564323889/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-462741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c212 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((36449/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log ((212 : ℕ)) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((212 : ℕ)) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3468817/10000000) (δ := 709/100000000) (ψ := 2829/500000) 281 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t212 : ((12513189039/1000000000000 : ℚ) : ℝ) ≤ stT281o2 212 := by
  have hc : ((36439/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12513189039/1000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((36439/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c213 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((149521/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log ((213 : ℕ)) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((213 : ℕ)) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1815869/10000000) (δ := 7213/1000000000) (ψ := 2829/500000) 281 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t213 : ((25610785767/500000000000 : ℚ) : ℝ) ≤ stT281o2 213 := by
  have hc : ((149511/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25610785767/500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((149511/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c214 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((997671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log ((214 : ℕ)) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((214 : ℕ)) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3413/200000) (δ := 719/100000000) (ψ := 2829/500000) 281 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t214 : ((136391750257/2000000000000 : ℚ) : ℝ) ≤ stT281o2 214 := by
  have hc : ((997621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136391750257/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((997621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c215 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((104093/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log ((215 : ℕ)) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((215 : ℕ)) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 733439/5000000) (δ := 7063/1000000000) (ψ := 2829/500000) 281 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t215 : ((141973077959/2500000000000 : ℚ) : ℝ) ≤ stT281o2 215 := by
  have hc : ((416347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141973077959/2500000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((416347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c216 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((163/500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log ((216 : ℕ)) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((216 : ℕ)) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1548409/5000000) (δ := 719/100000000) (ψ := 2829/500000) 281 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t216 : ((4435612347/200000000000 : ℚ) : ℝ) ≤ stT281o2 216 := by
  have hc : ((6519/20000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4435612347/200000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((6519/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c217 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-31161/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log ((217 : ℕ)) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((217 : ℕ)) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4719207/10000000) (δ := 11/1562500) (ψ := 2829/500000) 281 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t217 : ((-2115688327/100000000000 : ℚ) : ℝ) ≤ stT281o2 217 := by
  have hc : ((-15583/50000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2115688327/100000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-15583/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c218 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-82083/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log ((218 : ℕ)) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((218 : ℕ)) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6334149/10000000) (δ := 709/100000000) (ψ := 2829/500000) 281 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t218 : ((-3474815823/62500000000 : ℚ) : ℝ) ≤ stT281o2 218 := by
  have hc : ((-10261/12500 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3474815823/62500000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-10261/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c219 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-124923/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log ((219 : ℕ)) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((219 : ℕ)) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -970781/1250000) (δ := 89/12500000) (ψ := 2829/500000) 281 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t219 : ((-168838883073/2500000000000 : ℚ) : ℝ) ≤ stT281o2 219 := by
  have hc : ((-499717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168838883073/2500000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-499717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c220 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-48787/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log ((220 : ℕ)) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((220 : ℕ)) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6166023/10000000) (δ := 361/50000000) (ψ := 2829/500000) 281 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t220 : ((-1315772091/25000000000 : ℚ) : ℝ) ≤ stT281o2 220 := by
  have hc : ((-390321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1315772091/25000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-390321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c221 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-255551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log ((221 : ℕ)) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((221 : ℕ)) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2286517/5000000) (δ := 361/50000000) (ψ := 2829/500000) 281 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t221 : ((-171935891473/10000000000000 : ℚ) : ℝ) ≤ stT281o2 221 := by
  have hc : ((-255601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171935891473/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-255601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c222 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((73419/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log ((222 : ℕ)) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((222 : ℕ)) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2987281/10000000) (δ := 89/12500000) (ψ := 2829/500000) 281 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t222 : ((12317222701/500000000000 : ℚ) : ℝ) ≤ stT281o2 222 := by
  have hc : ((73409/200000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12317222701/500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((73409/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c223 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((422709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log ((223 : ℕ)) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((223 : ℕ)) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1408623/10000000) (δ := 89/12500000) (ψ := 2829/500000) 281 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t223 : ((70762479479/1250000000000 : ℚ) : ℝ) ≤ stT281o2 223 := by
  have hc : ((105671/125000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70762479479/1250000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((105671/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c224 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((249469/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log ((224 : ℕ)) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((224 : ℕ)) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6519/400000) (δ := 717/100000000) (ψ := 2829/500000) 281 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t224 : ((333350217689/5000000000000 : ℚ) : ℝ) ≤ stT281o2 224 := by
  have hc : ((498913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((333350217689/5000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((498913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c225 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((192647/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log ((225 : ℕ)) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((225 : ℕ)) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1727583/10000000) (δ := 717/100000000) (ψ := 2829/500000) 281 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t225 : ((128422871577/2500000000000 : ℚ) : ℝ) ≤ stT281o2 225 := by
  have hc : ((385269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128422871577/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((385269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c226 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((253899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log ((226 : ℕ)) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((226 : ℕ)) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1642609/5000000) (δ := 14183/1000000000) (ψ := 2829/500000) 281 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t226 : ((16885781631/1000000000000 : ℚ) : ℝ) ≤ stT281o2 226 := by
  have hc : ((253849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16885781631/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((253849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c227 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-177823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log ((227 : ℕ)) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((227 : ℕ)) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 967201/2000000) (δ := 717/100000000) (ψ := 2829/500000) 281 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t227 : ((-3688812061/156250000000 : ℚ) : ℝ) ≤ stT281o2 227 := by
  have hc : ((-22231/62500 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3688812061/156250000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-22231/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c228 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-415579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log ((228 : ℕ)) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((228 : ℕ)) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6379959/10000000) (δ := 7083/1000000000) (ψ := 2829/500000) 281 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t228 : ((-68810203567/1250000000000 : ℚ) : ℝ) ≤ stT281o2 228 := by
  have hc : ((-103901/125000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68810203567/1250000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-103901/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c229 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-999681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log ((229 : ℕ)) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((229 : ℕ)) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3895397/5000000) (δ := 897/125000000) (ψ := 2829/500000) 281 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t229 : ((-660641239689/10000000000000 : ℚ) : ℝ) ≤ stT281o2 229 := by
  have hc : ((-999731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-660641239689/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-999731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c230 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-803601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log ((230 : ℕ)) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((230 : ℕ)) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1565073/2500000) (δ := 7027/1000000000) (ψ := 2829/500000) 281 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t230 : ((-529912200031/10000000000000 : ℚ) : ℝ) ≤ stT281o2 230 := by
  have hc : ((-803651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-529912200031/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-803651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c231 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-79537/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log ((231 : ℕ)) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((231 : ℕ)) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4736429/10000000) (δ := 7027/1000000000) (ψ := 2829/500000) 281 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t231 : ((-3271234539/156250000000 : ℚ) : ℝ) ≤ stT281o2 231 := by
  have hc : ((-159099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3271234539/156250000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-159099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c232 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((279361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log ((232 : ℕ)) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((232 : ℕ)) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -321917/1000000) (δ := 3613/500000000) (ψ := 2829/500000) 281 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t232 : ((45844152363/2500000000000 : ℚ) : ℝ) ≤ stT281o2 232 := by
  have hc : ((279311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45844152363/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((279311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c233 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((387727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log ((233 : ℕ)) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((233 : ℕ)) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -213551/1250000) (δ := 7077/1000000000) (ψ := 2829/500000) 281 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t233 : ((126995860971/2500000000000 : ℚ) : ℝ) ≤ stT281o2 233 := by
  have hc : ((193851/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126995860971/2500000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((193851/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c234 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((996669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log ((234 : ℕ)) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((234 : ℕ)) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -20411/1000000) (δ := 3563/500000000) (ψ := 2829/500000) 281 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t234 : ((16287744317/250000000000 : ℚ) : ℝ) ≤ stT281o2 234 := by
  have hc : ((996619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16287744317/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((996619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c235 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((13579/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log ((235 : ℕ)) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((235 : ℕ)) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1293761/10000000) (δ := 7127/1000000000) (ψ := 2829/500000) 281 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t235 : ((35429809123/625000000000 : ℚ) : ℝ) ≤ stT281o2 235 := by
  have hc : ((434503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35429809123/625000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((434503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c236 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((440977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log ((236 : ℕ)) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((236 : ℕ)) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1392637/5000000) (δ := 7177/1000000000) (ψ := 2829/500000) 281 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t236 : ((4484668517/156250000000 : ℚ) : ℝ) ≤ stT281o2 236 := by
  have hc : ((440927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4484668517/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((440927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c237 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-136957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log ((237 : ℕ)) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((237 : ℕ)) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 33363/78125) (δ := 7027/1000000000) (ψ := 2829/500000) 281 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t237 : ((-8899563699/1000000000000 : ℚ) : ℝ) ≤ stT281o2 237 := by
  have hc : ((-137007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8899563699/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-137007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c238 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-333049/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log ((238 : ℕ)) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((238 : ℕ)) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2874701/5000000) (δ := 1769/250000000) (ψ := 2829/500000) 281 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t238 : ((-26987487387/625000000000 : ℚ) : ℝ) ≤ stT281o2 238 := by
  have hc : ((-166537/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26987487387/625000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-166537/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c239 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-484117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log ((239 : ℕ)) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((239 : ℕ)) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3611079/5000000) (δ := 3563/500000000) (ψ := 2829/500000) 281 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t239 : ((-156582900137/2500000000000 : ℚ) : ℝ) ≤ stT281o2 239 := by
  have hc : ((-242071/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156582900137/2500000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-242071/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c240 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-944767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log ((240 : ℕ)) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((240 : ℕ)) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1754799/2500000) (δ := 3559/500000000) (ψ := 2829/500000) 281 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t240 : ((-304938741933/5000000000000 : ℚ) : ℝ) ≤ stT281o2 240 := by
  have hc : ((-944817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304938741933/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-944817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c241 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-15183/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log ((241 : ℕ)) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((241 : ℕ)) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2779349/5000000) (δ := 1427/200000000) (ψ := 2829/500000) 281 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t241 : ((-39124163709/1000000000000 : ℚ) : ℝ) ≤ stT281o2 241 := by
  have hc : ((-60737/100000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39124163709/1000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-60737/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c242 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-70841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log ((242 : ℕ)) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((242 : ℕ)) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2052121/5000000) (δ := 1427/200000000) (ψ := 2829/500000) 281 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t242 : ((-1822820283/400000000000 : ℚ) : ℝ) ≤ stT281o2 242 := by
  have hc : ((-70891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1822820283/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-70891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c243 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((486849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log ((243 : ℕ)) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((243 : ℕ)) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2655793/10000000) (δ := 14/1953125) (ψ := 2829/500000) 281 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t243 : ((624563117/20000000000 : ℚ) : ℝ) ≤ stT281o2 243 := by
  have hc : ((486799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((624563117/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((486799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c244 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((88453/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log ((244 : ℕ)) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((244 : ℕ)) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1213279/10000000) (δ := 1417/200000000) (ψ := 2829/500000) 281 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t244 : ((55295893/976562500 : ℚ) : ℝ) ≤ stT281o2 244 := by
  have hc : ((2764/3125 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55295893/976562500 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((2764/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c245 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((996013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log ((245 : ℕ)) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((245 : ℕ)) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 55829/2500000) (δ := 2827/200000000) (ψ := 2829/500000) 281 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t245 : ((159074214397/2500000000000 : ℚ) : ℝ) ≤ stT281o2 245 := by
  have hc : ((995963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159074214397/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((995963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c246 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((788991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log ((246 : ℕ)) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((246 : ℕ)) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5169/31250) (δ := 1407/200000000) (ψ := 2829/500000) 281 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t246 : ((62876230877/1250000000000 : ℚ) : ℝ) ≤ stT281o2 246 := by
  have hc : ((788941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62876230877/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((788941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c247 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((166359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log ((247 : ℕ)) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((247 : ℕ)) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3079031/10000000) (δ := 1407/200000000) (ψ := 2829/500000) 281 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t247 : ((13229457857/625000000000 : ℚ) : ℝ) ≤ stT281o2 247 := by
  have hc : ((83167/250000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13229457857/625000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((83167/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c248 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-226509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log ((248 : ℕ)) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((248 : ℕ)) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4498221/10000000) (δ := 3609/500000000) (ψ := 2829/500000) 281 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t248 : ((-143865191559/10000000000000 : ℚ) : ℝ) ≤ stT281o2 248 := by
  have hc : ((-226559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143865191559/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-226559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c249 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-356539/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log ((249 : ℕ)) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((249 : ℕ)) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5911687/10000000) (δ := 1437/200000000) (ψ := 2829/500000) 281 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t249 : ((-2259635209/50000000000 : ℚ) : ℝ) ≤ stT281o2 249 := by
  have hc : ((-89141/125000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2259635209/50000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-89141/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_c250 :
    |Real.cos (((281 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((-244309/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log ((250 : ℕ)) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((250 : ℕ)) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1829883/2500000) (δ := 1427/200000000) (ψ := 2829/500000) 281 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st281o2_t250 : ((-38630649651/625000000000 : ℚ) : ℝ) ≤ stT281o2 250 := by
  have hc : ((-488643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((281 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st281o2_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38630649651/625000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-488643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st281o2_p1 : ((499967/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT281o2 (i+1) := by
  rw [Finset.sum_range_one]
  exact st281o2_t1

theorem st281o2_p2 : ((732034412427/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 1, stT281o2 (i+1)) + stT281o2 2 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 1
    simpa using h
  have hprev := st281o2_p1
  have hstep := st281o2_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p3 : ((-2364103460721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 2, stT281o2 (i+1)) + stT281o2 3 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 2
    simpa using h
  have hprev := st281o2_p2
  have hstep := st281o2_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p4 : ((2635396539279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 3, stT281o2 (i+1)) + stT281o2 4 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 3
    simpa using h
  have hprev := st281o2_p3
  have hstep := st281o2_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p5 : ((110858895501/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 4, stT281o2 (i+1)) + stT281o2 5 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 4
    simpa using h
  have hprev := st281o2_p4
  have hstep := st281o2_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p6 : ((677518976161/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 5, stT281o2 (i+1)) + stT281o2 6 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 5
    simpa using h
  have hprev := st281o2_p5
  have hstep := st281o2_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p7 : ((7071426827181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 6, stT281o2 (i+1)) + stT281o2 7 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 6
    simpa using h
  have hprev := st281o2_p6
  have hstep := st281o2_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p8 : ((3535981215531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 7, stT281o2 (i+1)) + stT281o2 8 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 7
    simpa using h
  have hprev := st281o2_p7
  have hstep := st281o2_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p9 : ((2894775495087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 8, stT281o2 (i+1)) + stT281o2 9 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 8
    simpa using h
  have hprev := st281o2_p8
  have hstep := st281o2_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p10 : ((82386391857/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 9, stT281o2 (i+1)) + stT281o2 10 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 9
    simpa using h
  have hprev := st281o2_p9
  have hstep := st281o2_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p11 : ((213207813663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 10, stT281o2 (i+1)) + stT281o2 11 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 10
    simpa using h
  have hprev := st281o2_p10
  have hstep := st281o2_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p12 : ((-1112368497473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 11, stT281o2 (i+1)) + stT281o2 12 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 11
    simpa using h
  have hprev := st281o2_p11
  have hstep := st281o2_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p13 : ((-3919581853531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 12, stT281o2 (i+1)) + stT281o2 13 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 12
    simpa using h
  have hprev := st281o2_p12
  have hstep := st281o2_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p14 : ((-1254410405339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 13, stT281o2 (i+1)) + stT281o2 14 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 13
    simpa using h
  have hprev := st281o2_p13
  have hstep := st281o2_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p15 : ((-737279234479/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 14, stT281o2 (i+1)) + stT281o2 15 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 14
    simpa using h
  have hprev := st281o2_p14
  have hstep := st281o2_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p16 : ((-237356234479/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 15, stT281o2 (i+1)) + stT281o2 16 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 15
    simpa using h
  have hprev := st281o2_p15
  have hstep := st281o2_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p17 : ((-2653433356007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 16, stT281o2 (i+1)) + stT281o2 17 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 16
    simpa using h
  have hprev := st281o2_p16
  have hstep := st281o2_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p18 : ((-265686467251/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 17, stT281o2 (i+1)) + stT281o2 18 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 17
    simpa using h
  have hprev := st281o2_p17
  have hstep := st281o2_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p19 : ((-3015839171257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 18, stT281o2 (i+1)) + stT281o2 19 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 18
    simpa using h
  have hprev := st281o2_p18
  have hstep := st281o2_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p20 : ((-196701150493/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 19, stT281o2 (i+1)) + stT281o2 20 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 19
    simpa using h
  have hprev := st281o2_p19
  have hstep := st281o2_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p21 : ((141906677009/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 20, stT281o2 (i+1)) + stT281o2 21 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 20
    simpa using h
  have hprev := st281o2_p20
  have hstep := st281o2_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p22 : ((1350442114247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 21, stT281o2 (i+1)) + stT281o2 22 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 21
    simpa using h
  have hprev := st281o2_p21
  have hstep := st281o2_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p23 : ((2142182759339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 22, stT281o2 (i+1)) + stT281o2 23 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 22
    simpa using h
  have hprev := st281o2_p22
  have hstep := st281o2_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p24 : ((1540143045957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 23, stT281o2 (i+1)) + stT281o2 24 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 23
    simpa using h
  have hprev := st281o2_p23
  have hstep := st281o2_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p25 : ((2035018545957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 24, stT281o2 (i+1)) + stT281o2 25 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 24
    simpa using h
  have hprev := st281o2_p24
  have hstep := st281o2_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p26 : ((9334909561917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 25, stT281o2 (i+1)) + stT281o2 26 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 25
    simpa using h
  have hprev := st281o2_p25
  have hstep := st281o2_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p27 : ((8719396407087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 26, stT281o2 (i+1)) + stT281o2 27 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 26
    simpa using h
  have hprev := st281o2_p26
  have hstep := st281o2_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p28 : ((3417172605081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 27, stT281o2 (i+1)) + stT281o2 28 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 27
    simpa using h
  have hprev := st281o2_p27
  have hstep := st281o2_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p29 : ((787969950087/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 28, stT281o2 (i+1)) + stT281o2 29 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 28
    simpa using h
  have hprev := st281o2_p28
  have hstep := st281o2_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p30 : ((4012298587159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 29, stT281o2 (i+1)) + stT281o2 30 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 29
    simpa using h
  have hprev := st281o2_p29
  have hstep := st281o2_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p31 : ((67542737923/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 30, stT281o2 (i+1)) + stT281o2 31 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 30
    simpa using h
  have hprev := st281o2_p30
  have hstep := st281o2_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p32 : ((6675230803871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 31, stT281o2 (i+1)) + stT281o2 32 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 31
    simpa using h
  have hprev := st281o2_p31
  have hstep := st281o2_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p33 : ((7361998269839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 32, stT281o2 (i+1)) + stT281o2 33 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 32
    simpa using h
  have hprev := st281o2_p32
  have hstep := st281o2_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p34 : ((8395911276789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 33, stT281o2 (i+1)) + stT281o2 34 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 33
    simpa using h
  have hprev := st281o2_p33
  have hstep := st281o2_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p35 : ((6705565089991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 34, stT281o2 (i+1)) + stT281o2 35 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 34
    simpa using h
  have hprev := st281o2_p34
  have hstep := st281o2_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p36 : ((7837719637129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 35, stT281o2 (i+1)) + stT281o2 36 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 35
    simpa using h
  have hprev := st281o2_p35
  have hstep := st281o2_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p37 : ((7773702666529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 36, stT281o2 (i+1)) + stT281o2 37 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 36
    simpa using h
  have hprev := st281o2_p36
  have hstep := st281o2_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p38 : ((862894853893/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 37, stT281o2 (i+1)) + stT281o2 38 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 37
    simpa using h
  have hprev := st281o2_p37
  have hstep := st281o2_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p39 : ((8311057928617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 38, stT281o2 (i+1)) + stT281o2 39 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 38
    simpa using h
  have hprev := st281o2_p38
  have hstep := st281o2_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p40 : ((3367504307529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 39, stT281o2 (i+1)) + stT281o2 40 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 39
    simpa using h
  have hprev := st281o2_p39
  have hstep := st281o2_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p41 : ((329973313659/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 40, stT281o2 (i+1)) + stT281o2 41 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 40
    simpa using h
  have hprev := st281o2_p40
  have hstep := st281o2_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p42 : ((6888480236753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 41, stT281o2 (i+1)) + stT281o2 42 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 41
    simpa using h
  have hprev := st281o2_p41
  have hstep := st281o2_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p43 : ((8097421245413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 42, stT281o2 (i+1)) + stT281o2 43 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 42
    simpa using h
  have hprev := st281o2_p42
  have hstep := st281o2_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p44 : ((3493981657423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 43, stT281o2 (i+1)) + stT281o2 44 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 43
    simpa using h
  have hprev := st281o2_p43
  have hstep := st281o2_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p45 : ((8068754131933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 44, stT281o2 (i+1)) + stT281o2 45 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 44
    simpa using h
  have hprev := st281o2_p44
  have hstep := st281o2_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p46 : ((6946804553873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 45, stT281o2 (i+1)) + stT281o2 46 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 45
    simpa using h
  have hprev := st281o2_p45
  have hstep := st281o2_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p47 : ((8161897095747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 46, stT281o2 (i+1)) + stT281o2 47 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 46
    simpa using h
  have hprev := st281o2_p46
  have hstep := st281o2_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p48 : ((6833830961011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 47, stT281o2 (i+1)) + stT281o2 48 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 47
    simpa using h
  have hprev := st281o2_p47
  have hstep := st281o2_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p49 : ((412227169747/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 48, stT281o2 (i+1)) + stT281o2 49 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 48
    simpa using h
  have hprev := st281o2_p48
  have hstep := st281o2_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p50 : ((3422563158011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 49, stT281o2 (i+1)) + stT281o2 50 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 49
    simpa using h
  have hprev := st281o2_p49
  have hstep := st281o2_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p51 : ((4035455211911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 50, stT281o2 (i+1)) + stT281o2 51 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 50
    simpa using h
  have hprev := st281o2_p50
  have hstep := st281o2_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p52 : ((7228305261961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 51, stT281o2 (i+1)) + stT281o2 52 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 51
    simpa using h
  have hprev := st281o2_p51
  have hstep := st281o2_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p53 : ((7484504572141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 52, stT281o2 (i+1)) + stT281o2 53 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 52
    simpa using h
  have hprev := st281o2_p52
  have hstep := st281o2_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p54 : ((7922424144049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 53, stT281o2 (i+1)) + stT281o2 54 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 53
    simpa using h
  have hprev := st281o2_p53
  have hstep := st281o2_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p55 : ((6873509177649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 54, stT281o2 (i+1)) + stT281o2 55 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 54
    simpa using h
  have hprev := st281o2_p54
  have hstep := st281o2_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p56 : ((1641303167627/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 55, stT281o2 (i+1)) + stT281o2 56 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 55
    simpa using h
  have hprev := st281o2_p55
  have hstep := st281o2_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p57 : ((7102337446147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 56, stT281o2 (i+1)) + stT281o2 57 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 56
    simpa using h
  have hprev := st281o2_p56
  have hstep := st281o2_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p58 : ((7474629169003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 57, stT281o2 (i+1)) + stT281o2 58 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 57
    simpa using h
  have hprev := st281o2_p57
  have hstep := st281o2_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p59 : ((8043541643113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 58, stT281o2 (i+1)) + stT281o2 59 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 58
    simpa using h
  have hprev := st281o2_p58
  have hstep := st281o2_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p60 : ((6825653107973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 59, stT281o2 (i+1)) + stT281o2 60 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 59
    simpa using h
  have hprev := st281o2_p59
  have hstep := st281o2_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p61 : ((7960718545493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 60, stT281o2 (i+1)) + stT281o2 61 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 60
    simpa using h
  have hprev := st281o2_p60
  have hstep := st281o2_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p62 : ((7667570333843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 61, stT281o2 (i+1)) + stT281o2 62 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 61
    simpa using h
  have hprev := st281o2_p61
  have hstep := st281o2_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p63 : ((6894393349263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 62, stT281o2 (i+1)) + stT281o2 63 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 62
    simpa using h
  have hprev := st281o2_p62
  have hstep := st281o2_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p64 : ((8144109599263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 63, stT281o2 (i+1)) + stT281o2 64 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 63
    simpa using h
  have hprev := st281o2_p63
  have hstep := st281o2_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p65 : ((7455284818159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 64, stT281o2 (i+1)) + stT281o2 65 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 64
    simpa using h
  have hprev := st281o2_p64
  have hstep := st281o2_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p66 : ((6967067001709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 65, stT281o2 (i+1)) + stT281o2 66 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 65
    simpa using h
  have hprev := st281o2_p65
  have hstep := st281o2_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p67 : ((8177708336091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 66, stT281o2 (i+1)) + stT281o2 67 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 66
    simpa using h
  have hprev := st281o2_p66
  have hstep := st281o2_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p68 : ((931077531879/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 67, stT281o2 (i+1)) + stT281o2 68 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 67
    simpa using h
  have hprev := st281o2_p67
  have hstep := st281o2_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p69 : ((6929811199687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 68, stT281o2 (i+1)) + stT281o2 69 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 68
    simpa using h
  have hprev := st281o2_p68
  have hstep := st281o2_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p70 : ((1624992541019/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 69, stT281o2 (i+1)) + stT281o2 70 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 69
    simpa using h
  have hprev := st281o2_p69
  have hstep := st281o2_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p71 : ((7632909833293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 70, stT281o2 (i+1)) + stT281o2 71 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 70
    simpa using h
  have hprev := st281o2_p70
  have hstep := st281o2_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p72 : ((1366068867961/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 71, stT281o2 (i+1)) + stT281o2 72 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 71
    simpa using h
  have hprev := st281o2_p71
  have hstep := st281o2_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p73 : ((1583276082163/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 72, stT281o2 (i+1)) + stT281o2 73 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 72
    simpa using h
  have hprev := st281o2_p72
  have hstep := st281o2_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p74 : ((7964091913283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 73, stT281o2 (i+1)) + stT281o2 74 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 73
    simpa using h
  have hprev := st281o2_p73
  have hstep := st281o2_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p75 : ((6852422000749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 74, stT281o2 (i+1)) + stT281o2 75 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 74
    simpa using h
  have hprev := st281o2_p74
  have hstep := st281o2_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p76 : ((7465751989491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 75, stT281o2 (i+1)) + stT281o2 76 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 75
    simpa using h
  have hprev := st281o2_p75
  have hstep := st281o2_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p77 : ((8234759722701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 76, stT281o2 (i+1)) + stT281o2 77 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 76
    simpa using h
  have hprev := st281o2_p76
  have hstep := st281o2_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p78 : ((7240293542637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 77, stT281o2 (i+1)) + stT281o2 78 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 77
    simpa using h
  have hprev := st281o2_p77
  have hstep := st281o2_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p79 : ((6929746752877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 78, stT281o2 (i+1)) + stT281o2 79 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 78
    simpa using h
  have hprev := st281o2_p78
  have hstep := st281o2_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p80 : ((804386775541/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 79, stT281o2 (i+1)) + stT281o2 80 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 79
    simpa using h
  have hprev := st281o2_p79
  have hstep := st281o2_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p81 : ((3971148281521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 80, stT281o2 (i+1)) + stT281o2 81 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 80
    simpa using h
  have hprev := st281o2_p80
  have hstep := st281o2_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p82 : ((3435403730229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 81, stT281o2 (i+1)) + stT281o2 82 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 81
    simpa using h
  have hprev := st281o2_p81
  have hstep := st281o2_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p83 : ((3637366565303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 82, stT281o2 (i+1)) + stT281o2 83 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 82
    simpa using h
  have hprev := st281o2_p82
  have hstep := st281o2_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p84 : ((8238019602769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 83, stT281o2 (i+1)) + stT281o2 84 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 83
    simpa using h
  have hprev := st281o2_p83
  have hstep := st281o2_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p85 : ((7642913887789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 84, stT281o2 (i+1)) + stT281o2 85 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 84
    simpa using h
  have hprev := st281o2_p84
  have hstep := st281o2_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p86 : ((1357301589369/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 85, stT281o2 (i+1)) + stT281o2 86 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 85
    simpa using h
  have hprev := st281o2_p85
  have hstep := st281o2_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p87 : ((1496521765241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 86, stT281o2 (i+1)) + stT281o2 87 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 86
    simpa using h
  have hprev := st281o2_p86
  have hstep := st281o2_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p88 : ((516786668509/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 87, stT281o2 (i+1)) + stT281o2 88 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 87
    simpa using h
  have hprev := st281o2_p87
  have hstep := st281o2_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p89 : ((3769745725899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 88, stT281o2 (i+1)) + stT281o2 89 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 88
    simpa using h
  have hprev := st281o2_p88
  have hstep := st281o2_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p90 : ((3386781089883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 89, stT281o2 (i+1)) + stT281o2 90 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 89
    simpa using h
  have hprev := st281o2_p89
  have hstep := st281o2_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p91 : ((3739860961911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 90, stT281o2 (i+1)) + stT281o2 91 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 90
    simpa using h
  have hprev := st281o2_p90
  have hstep := st281o2_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p92 : ((4137217992129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 91, stT281o2 (i+1)) + stT281o2 92 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 91
    simpa using h
  have hprev := st281o2_p91
  have hstep := st281o2_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p93 : ((764514196097/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 92, stT281o2 (i+1)) + stT281o2 93 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 92
    simpa using h
  have hprev := st281o2_p92
  have hstep := st281o2_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p94 : ((3392290601901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 93, stT281o2 (i+1)) + stT281o2 94 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 93
    simpa using h
  have hprev := st281o2_p93
  have hstep := st281o2_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p95 : ((3638175463403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 94, stT281o2 (i+1)) + stT281o2 95 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 94
    simpa using h
  have hprev := st281o2_p94
  have hstep := st281o2_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p96 : ((4108105653723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 95, stT281o2 (i+1)) + stT281o2 96 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 95
    simpa using h
  have hprev := st281o2_p95
  have hstep := st281o2_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p97 : ((7930168765953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 96, stT281o2 (i+1)) + stT281o2 97 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 96
    simpa using h
  have hprev := st281o2_p96
  have hstep := st281o2_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p98 : ((6932196190827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 97, stT281o2 (i+1)) + stT281o2 98 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 97
    simpa using h
  have hprev := st281o2_p97
  have hstep := st281o2_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p99 : ((6943593310407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 98, stT281o2 (i+1)) + stT281o2 99 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 98
    simpa using h
  have hprev := st281o2_p98
  have hstep := st281o2_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p100 : ((1983176830323/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 99, stT281o2 (i+1)) + stT281o2 100 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 99
    simpa using h
  have hprev := st281o2_p99
  have hstep := st281o2_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p101 : ((8245760887047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 100, stT281o2 (i+1)) + stT281o2 101 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 100
    simpa using h
  have hprev := st281o2_p100
  have hstep := st281o2_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p102 : ((1475990342459/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 101, stT281o2 (i+1)) + stT281o2 102 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 101
    simpa using h
  have hprev := st281o2_p101
  have hstep := st281o2_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p103 : ((1348017652719/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 102, stT281o2 (i+1)) + stT281o2 103 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 102
    simpa using h
  have hprev := st281o2_p102
  have hstep := st281o2_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p104 : ((1466816488647/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 103, stT281o2 (i+1)) + stT281o2 104 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 103
    simpa using h
  have hprev := st281o2_p103
  have hstep := st281o2_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p105 : ((1644663528747/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 104, stT281o2 (i+1)) + stT281o2 105 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 104
    simpa using h
  have hprev := st281o2_p104
  have hstep := st281o2_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p106 : ((8044164912321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 105, stT281o2 (i+1)) + stT281o2 106 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 105
    simpa using h
  have hprev := st281o2_p105
  have hstep := st281o2_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p107 : ((1415897799121/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 106, stT281o2 (i+1)) + stT281o2 107 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 106
    simpa using h
  have hprev := st281o2_p106
  have hstep := st281o2_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p108 : ((6767740841127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 107, stT281o2 (i+1)) + stT281o2 108 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 107
    simpa using h
  have hprev := st281o2_p107
  have hstep := st281o2_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p109 : ((7555102547907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 108, stT281o2 (i+1)) + stT281o2 109 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 108
    simpa using h
  have hprev := st281o2_p108
  have hstep := st281o2_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p110 : ((8298012487909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 109, stT281o2 (i+1)) + stT281o2 110 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 109
    simpa using h
  have hprev := st281o2_p109
  have hstep := st281o2_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p111 : ((7947588100099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 110, stT281o2 (i+1)) + stT281o2 111 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 110
    simpa using h
  have hprev := st281o2_p110
  have hstep := st281o2_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p112 : ((7004772859827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 111, stT281o2 (i+1)) + stT281o2 112 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 111
    simpa using h
  have hprev := st281o2_p111
  have hstep := st281o2_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p113 : ((1353575723233/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 112, stT281o2 (i+1)) + stT281o2 113 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 112
    simpa using h
  have hprev := st281o2_p112
  have hstep := st281o2_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p114 : ((1509484157941/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 113, stT281o2 (i+1)) + stT281o2 114 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 113
    simpa using h
  have hprev := st281o2_p113
  have hstep := st281o2_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p115 : ((1659103492237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 114, stT281o2 (i+1)) + stT281o2 115 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 114
    simpa using h
  have hprev := st281o2_p114
  have hstep := st281o2_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p116 : ((8034138187007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 115, stT281o2 (i+1)) + stT281o2 116 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 115
    simpa using h
  have hprev := st281o2_p115
  have hstep := st281o2_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p117 : ((1778126940653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 116, stT281o2 (i+1)) + stT281o2 117 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 116
    simpa using h
  have hprev := st281o2_p116
  have hstep := st281o2_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p118 : ((838540012889/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 117, stT281o2 (i+1)) + stT281o2 118 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 117
    simpa using h
  have hprev := st281o2_p117
  have hstep := st281o2_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p119 : ((915047627969/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 118, stT281o2 (i+1)) + stT281o2 119 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 118
    simpa using h
  have hprev := st281o2_p118
  have hstep := st281o2_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p120 : ((511382915767/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 119, stT281o2 (i+1)) + stT281o2 120 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 119
    simpa using h
  have hprev := st281o2_p119
  have hstep := st281o2_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p121 : ((2061123920203/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 120, stT281o2 (i+1)) + stT281o2 121 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 120
    simpa using h
  have hprev := st281o2_p120
  have hstep := st281o2_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p122 : ((744271154137/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 121, stT281o2 (i+1)) + stT281o2 122 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 121
    simpa using h
  have hprev := st281o2_p121
  have hstep := st281o2_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p123 : ((336623619703/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 122, stT281o2 (i+1)) + stT281o2 123 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 122
    simpa using h
  have hprev := st281o2_p122
  have hstep := st281o2_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p124 : ((1734438488363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 123, stT281o2 (i+1)) + stT281o2 124 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 123
    simpa using h
  have hprev := st281o2_p123
  have hstep := st281o2_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p125 : ((1953047180287/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 124, stT281o2 (i+1)) + stT281o2 125 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 124
    simpa using h
  have hprev := st281o2_p124
  have hstep := st281o2_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p126 : ((4180178979339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 125, stT281o2 (i+1)) + stT281o2 126 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 125
    simpa using h
  have hprev := st281o2_p125
  have hstep := st281o2_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p127 : ((7976092446613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 126, stT281o2 (i+1)) + stT281o2 127 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 126
    simpa using h
  have hprev := st281o2_p126
  have hstep := st281o2_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p128 : ((7092359590777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 127, stT281o2 (i+1)) + stT281o2 128 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 127
    simpa using h
  have hprev := st281o2_p127
  have hstep := st281o2_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p129 : ((6671433576697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 128, stT281o2 (i+1)) + stT281o2 129 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 128
    simpa using h
  have hprev := st281o2_p128
  have hstep := st281o2_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p130 : ((7156818523289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 129, stT281o2 (i+1)) + stT281o2 130 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 129
    simpa using h
  have hprev := st281o2_p129
  have hstep := st281o2_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p131 : ((8026754237937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 130, stT281o2 (i+1)) + stT281o2 131 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 130
    simpa using h
  have hprev := st281o2_p130
  have hstep := st281o2_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p132 : ((8373638671457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 131, stT281o2 (i+1)) + stT281o2 132 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 131
    simpa using h
  have hprev := st281o2_p131
  have hstep := st281o2_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p133 : ((7848554141187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 132, stT281o2 (i+1)) + stT281o2 133 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 132
    simpa using h
  have hprev := st281o2_p132
  have hstep := st281o2_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p134 : ((3496080963691/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 133, stT281o2 (i+1)) + stT281o2 134 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 133
    simpa using h
  have hprev := st281o2_p133
  have hstep := st281o2_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p135 : ((6661609670961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 134, stT281o2 (i+1)) + stT281o2 135 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 134
    simpa using h
  have hprev := st281o2_p134
  have hstep := st281o2_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p136 : ((7175554361097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 135, stT281o2 (i+1)) + stT281o2 136 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 135
    simpa using h
  have hprev := st281o2_p135
  have hstep := st281o2_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p137 : ((4012745031811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 136, stT281o2 (i+1)) + stT281o2 137 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 136
    simpa using h
  have hprev := st281o2_p136
  have hstep := st281o2_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p138 : ((4196975557843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 137, stT281o2 (i+1)) + stT281o2 138 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 137
    simpa using h
  have hprev := st281o2_p137
  have hstep := st281o2_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p139 : ((793852112127/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 138, stT281o2 (i+1)) + stT281o2 139 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 138
    simpa using h
  have hprev := st281o2_p138
  have hstep := st281o2_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p140 : ((1418665617859/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 139, stT281o2 (i+1)) + stT281o2 140 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 139
    simpa using h
  have hprev := st281o2_p139
  have hstep := st281o2_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p141 : ((1328097223171/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 140, stT281o2 (i+1)) + stT281o2 141 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 140
    simpa using h
  have hprev := st281o2_p140
  have hstep := st281o2_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p142 : ((436666409027/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 141, stT281o2 (i+1)) + stT281o2 142 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 141
    simpa using h
  have hprev := st281o2_p141
  have hstep := st281o2_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p143 : ((488265049153/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 142, stT281o2 (i+1)) + stT281o2 143 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 142
    simpa using h
  have hprev := st281o2_p142
  have hstep := st281o2_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p144 : ((261906267467/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 143, stT281o2 (i+1)) + stT281o2 144 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 143
    simpa using h
  have hprev := st281o2_p143
  have hstep := st281o2_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p145 : ((4099431753717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 144, stT281o2 (i+1)) + stT281o2 145 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 144
    simpa using h
  have hprev := st281o2_p144
  have hstep := st281o2_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p146 : ((3715756922541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 145, stT281o2 (i+1)) + stT281o2 146 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 145
    simpa using h
  have hprev := st281o2_p145
  have hstep := st281o2_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p147 : ((3369648254583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 146, stT281o2 (i+1)) + stT281o2 147 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 146
    simpa using h
  have hprev := st281o2_p146
  have hstep := st281o2_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p148 : ((6703678643821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 147, stT281o2 (i+1)) + stT281o2 148 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 147
    simpa using h
  have hprev := st281o2_p147
  have hstep := st281o2_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p149 : ((3673405102877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 148, stT281o2 (i+1)) + stT281o2 149 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 148
    simpa using h
  have hprev := st281o2_p148
  have hstep := st281o2_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p150 : ((4066641007421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 149, stT281o2 (i+1)) + stT281o2 150 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 149
    simpa using h
  have hprev := st281o2_p149
  have hstep := st281o2_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p151 : ((4212009585437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 150, stT281o2 (i+1)) + stT281o2 151 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 150
    simpa using h
  have hprev := st281o2_p150
  have hstep := st281o2_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p152 : ((3995874853339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 151, stT281o2 (i+1)) + stT281o2 152 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 151
    simpa using h
  have hprev := st281o2_p151
  have hstep := st281o2_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p153 : ((7186346999847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 152, stT281o2 (i+1)) + stT281o2 153 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 152
    simpa using h
  have hprev := st281o2_p152
  have hstep := st281o2_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p154 : ((6641194847179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 153, stT281o2 (i+1)) + stT281o2 154 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 153
    simpa using h
  have hprev := st281o2_p153
  have hstep := st281o2_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p155 : ((846777495233/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 154, stT281o2 (i+1)) + stT281o2 155 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 154
    simpa using h
  have hprev := st281o2_p154
  have hstep := st281o2_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p156 : ((934561466273/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 155, stT281o2 (i+1)) + stT281o2 156 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 155
    simpa using h
  have hprev := st281o2_p155
  have hstep := st281o2_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p157 : ((4106242122563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 156, stT281o2 (i+1)) + stT281o2 157 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 156
    simpa using h
  have hprev := st281o2_p156
  have hstep := st281o2_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p158 : ((8433668980051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 157, stT281o2 (i+1)) + stT281o2 158 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 157
    simpa using h
  have hprev := st281o2_p157
  have hstep := st281o2_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p159 : ((7982797505647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 158, stT281o2 (i+1)) + stT281o2 159 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 158
    simpa using h
  have hprev := st281o2_p158
  have hstep := st281o2_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p160 : ((7195060117957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 159, stT281o2 (i+1)) + stT281o2 160 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 159
    simpa using h
  have hprev := st281o2_p159
  have hstep := st281o2_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p161 : ((6640379715047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 160, stT281o2 (i+1)) + stT281o2 161 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 160
    simpa using h
  have hprev := st281o2_p160
  have hstep := st281o2_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p162 : ((1342081682003/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 161, stT281o2 (i+1)) + stT281o2 162 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 161
    simpa using h
  have hprev := st281o2_p161
  have hstep := st281o2_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p163 : ((293970695187/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 162, stT281o2 (i+1)) + stT281o2 163 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 162
    simpa using h
  have hprev := st281o2_p162
  have hstep := st281o2_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p164 : ((8107257509011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 163, stT281o2 (i+1)) + stT281o2 164 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 163
    simpa using h
  have hprev := st281o2_p163
  have hstep := st281o2_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p165 : ((8462732151779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 164, stT281o2 (i+1)) + stT281o2 165 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 164
    simpa using h
  have hprev := st281o2_p164
  have hstep := st281o2_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p166 : ((4089313755643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 165, stT281o2 (i+1)) + stT281o2 166 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 165
    simpa using h
  have hprev := st281o2_p165
  have hstep := st281o2_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p167 : ((3726138033019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 166, stT281o2 (i+1)) + stT281o2 167 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 166
    simpa using h
  have hprev := st281o2_p166
  have hstep := st281o2_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p168 : ((6770257352589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 167, stT281o2 (i+1)) + stT281o2 168 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 167
    simpa using h
  have hprev := st281o2_p167
  have hstep := st281o2_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p169 : ((328980595539/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 168, stT281o2 (i+1)) + stT281o2 169 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 168
    simpa using h
  have hprev := st281o2_p168
  have hstep := st281o2_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p170 : ((874866479701/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 169, stT281o2 (i+1)) + stT281o2 170 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 169
    simpa using h
  have hprev := st281o2_p169
  have hstep := st281o2_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p171 : ((7752815534097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 170, stT281o2 (i+1)) + stT281o2 171 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 170
    simpa using h
  have hprev := st281o2_p170
  have hstep := st281o2_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p172 : ((8359322258181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 171, stT281o2 (i+1)) + stT281o2 172 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 171
    simpa using h
  have hprev := st281o2_p171
  have hstep := st281o2_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p173 : ((4219597759713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 172, stT281o2 (i+1)) + stT281o2 173 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 172
    simpa using h
  have hprev := st281o2_p172
  have hstep := st281o2_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p174 : ((7948174039027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 173, stT281o2 (i+1)) + stT281o2 174 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 173
    simpa using h
  have hprev := st281o2_p173
  have hstep := st281o2_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p175 : ((7193619317949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 174, stT281o2 (i+1)) + stT281o2 175 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 174
    simpa using h
  have hprev := st281o2_p174
  have hstep := st281o2_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p176 : ((6636652014849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 175, stT281o2 (i+1)) + stT281o2 176 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 175
    simpa using h
  have hprev := st281o2_p175
  have hstep := st281o2_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p177 : ((6610073776929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 176, stT281o2 (i+1)) + stT281o2 177 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 176
    simpa using h
  have hprev := st281o2_p176
  have hstep := st281o2_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p178 : ((3562176614807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 177, stT281o2 (i+1)) + stT281o2 178 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 177
    simpa using h
  have hprev := st281o2_p177
  have hstep := st281o2_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p179 : ((245983431947/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 178, stT281o2 (i+1)) + stT281o2 179 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 178
    simpa using h
  have hprev := st281o2_p178
  have hstep := st281o2_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p180 : ((8414108386889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 179, stT281o2 (i+1)) + stT281o2 180 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 179
    simpa using h
  have hprev := st281o2_p179
  have hstep := st281o2_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p181 : ((8441651889353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 180, stT281o2 (i+1)) + stT281o2 181 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 180
    simpa using h
  have hprev := st281o2_p180
  have hstep := st281o2_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p182 : ((7943451834353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 181, stT281o2 (i+1)) + stT281o2 182 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 181
    simpa using h
  have hprev := st281o2_p181
  have hstep := st281o2_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p183 : ((7205703843021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 182, stT281o2 (i+1)) + stT281o2 183 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 182
    simpa using h
  have hprev := st281o2_p182
  have hstep := st281o2_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p184 : ((6642638326431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 183, stT281o2 (i+1)) + stT281o2 184 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 183
    simpa using h
  have hprev := st281o2_p183
  have hstep := st281o2_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p185 : ((6563685058011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 184, stT281o2 (i+1)) + stT281o2 185 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 184
    simpa using h
  have hprev := st281o2_p184
  have hstep := st281o2_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p186 : ((7007311297121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 185, stT281o2 (i+1)) + stT281o2 186 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 185
    simpa using h
  have hprev := st281o2_p185
  have hstep := st281o2_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p187 : ((1545660615069/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 186, stT281o2 (i+1)) + stT281o2 187 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 186
    simpa using h
  have hprev := st281o2_p186
  have hstep := st281o2_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p188 : ((8337616081821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 187, stT281o2 (i+1)) + stT281o2 188 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 187
    simpa using h
  have hprev := st281o2_p187
  have hstep := st281o2_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p189 : ((8513077580061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 188, stT281o2 (i+1)) + stT281o2 189 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 188
    simpa using h
  have hprev := st281o2_p188
  have hstep := st281o2_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p190 : ((8166666665423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 189, stT281o2 (i+1)) + stT281o2 190 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 189
    simpa using h
  have hprev := st281o2_p189
  have hstep := st281o2_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p191 : ((7483400581523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 190, stT281o2 (i+1)) + stT281o2 191 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 190
    simpa using h
  have hprev := st281o2_p190
  have hstep := st281o2_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p192 : ((6818131262611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 191, stT281o2 (i+1)) + stT281o2 192 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 191
    simpa using h
  have hprev := st281o2_p191
  have hstep := st281o2_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p193 : ((1301940036807/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 192, stT281o2 (i+1)) + stT281o2 193 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 192
    simpa using h
  have hprev := st281o2_p192
  have hstep := st281o2_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p194 : ((6710380932363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 193, stT281o2 (i+1)) + stT281o2 194 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 193
    simpa using h
  have hprev := st281o2_p193
  have hstep := st281o2_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p195 : ((7315133476451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 194, stT281o2 (i+1)) + stT281o2 195 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 194
    simpa using h
  have hprev := st281o2_p194
  have hstep := st281o2_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p196 : ((4010487456733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 195, stT281o2 (i+1)) + stT281o2 196 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 195
    simpa using h
  have hprev := st281o2_p195
  have hstep := st281o2_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p197 : ((4240559694073/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 196, stT281o2 (i+1)) + stT281o2 197 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 196
    simpa using h
  have hprev := st281o2_p196
  have hstep := st281o2_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p198 : ((4237272845323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 197, stT281o2 (i+1)) + stT281o2 198 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 197
    simpa using h
  have hprev := st281o2_p197
  have hstep := st281o2_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p199 : ((4004339891179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 198, stT281o2 (i+1)) + stT281o2 199 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 198
    simpa using h
  have hprev := st281o2_p198
  have hstep := st281o2_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p200 : ((7309428034021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 199, stT281o2 (i+1)) + stT281o2 200 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 199
    simpa using h
  have hprev := st281o2_p199
  have hstep := st281o2_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p201 : ((6708521205549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 200, stT281o2 (i+1)) + stT281o2 201 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 200
    simpa using h
  have hprev := st281o2_p200
  have hstep := st281o2_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p202 : ((6485616433963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 201, stT281o2 (i+1)) + stT281o2 202 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 201
    simpa using h
  have hprev := st281o2_p201
  have hstep := st281o2_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p203 : ((6740381812033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 202, stT281o2 (i+1)) + stT281o2 203 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 202
    simpa using h
  have hprev := st281o2_p202
  have hstep := st281o2_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p204 : ((7351780467313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 203, stT281o2 (i+1)) + stT281o2 204 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 203
    simpa using h
  have hprev := st281o2_p203
  have hstep := st281o2_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p205 : ((8039116605193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 204, stT281o2 (i+1)) + stT281o2 205 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 204
    simpa using h
  have hprev := st281o2_p204
  have hstep := st281o2_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p206 : ((339706309539/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 205, stT281o2 (i+1)) + stT281o2 206 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 205
    simpa using h
  have hprev := st281o2_p205
  have hstep := st281o2_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p207 : ((8512444364939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 206, stT281o2 (i+1)) + stT281o2 207 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 206
    simpa using h
  have hprev := st281o2_p206
  have hstep := st281o2_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p208 : ((8093566909451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 207, stT281o2 (i+1)) + stT281o2 208 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 207
    simpa using h
  have hprev := st281o2_p207
  have hstep := st281o2_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p209 : ((7423037756471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 208, stT281o2 (i+1)) + stT281o2 209 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 208
    simpa using h
  have hprev := st281o2_p208
  have hstep := st281o2_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p210 : ((6793563001601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 209, stT281o2 (i+1)) + stT281o2 210 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 209
    simpa using h
  have hprev := st281o2_p209
  have hstep := st281o2_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p211 : ((404687417357/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 210, stT281o2 (i+1)) + stT281o2 211 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 210
    simpa using h
  have hprev := st281o2_p210
  have hstep := st281o2_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p212 : ((3300065284051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 211, stT281o2 (i+1)) + stT281o2 212 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 211
    simpa using h
  have hprev := st281o2_p211
  have hstep := st281o2_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p213 : ((3556173141721/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 212, stT281o2 (i+1)) + stT281o2 213 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 212
    simpa using h
  have hprev := st281o2_p212
  have hstep := st281o2_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p214 : ((7794305034727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 213, stT281o2 (i+1)) + stT281o2 214 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 213
    simpa using h
  have hprev := st281o2_p213
  have hstep := st281o2_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p215 : ((8362197346563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 214, stT281o2 (i+1)) + stT281o2 215 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 214
    simpa using h
  have hprev := st281o2_p214
  have hstep := st281o2_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p216 : ((8583977963913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 215, stT281o2 (i+1)) + stT281o2 216 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 215
    simpa using h
  have hprev := st281o2_p215
  have hstep := st281o2_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p217 : ((8372409131213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 216, stT281o2 (i+1)) + stT281o2 217 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 216
    simpa using h
  have hprev := st281o2_p216
  have hstep := st281o2_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p218 : ((7816438599533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 217, stT281o2 (i+1)) + stT281o2 218 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 217
    simpa using h
  have hprev := st281o2_p217
  have hstep := st281o2_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p219 : ((7141083067241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 218, stT281o2 (i+1)) + stT281o2 219 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 218
    simpa using h
  have hprev := st281o2_p218
  have hstep := st281o2_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p220 : ((6614774230841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 219, stT281o2 (i+1)) + stT281o2 220 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 219
    simpa using h
  have hprev := st281o2_p219
  have hstep := st281o2_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p221 : ((805354792421/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 220, stT281o2 (i+1)) + stT281o2 221 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 220
    simpa using h
  have hprev := st281o2_p220
  have hstep := st281o2_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p222 : ((1672295698347/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 221, stT281o2 (i+1)) + stT281o2 222 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 221
    simpa using h
  have hprev := st281o2_p221
  have hstep := st281o2_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p223 : ((362764131461/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 222, stT281o2 (i+1)) + stT281o2 223 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 222
    simpa using h
  have hprev := st281o2_p222
  have hstep := st281o2_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p224 : ((3960991532299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 223, stT281o2 (i+1)) + stT281o2 224 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 223
    simpa using h
  have hprev := st281o2_p223
  have hstep := st281o2_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p225 : ((4217837275453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 224, stT281o2 (i+1)) + stT281o2 225 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 224
    simpa using h
  have hprev := st281o2_p224
  have hstep := st281o2_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p226 : ((537783272951/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 225, stT281o2 (i+1)) + stT281o2 226 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 225
    simpa using h
  have hprev := st281o2_p225
  have hstep := st281o2_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p227 : ((523028024707/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 226, stT281o2 (i+1)) + stT281o2 227 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 226
    simpa using h
  have hprev := st281o2_p226
  have hstep := st281o2_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p228 : ((977245845847/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 227, stT281o2 (i+1)) + stT281o2 228 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 227
    simpa using h
  have hprev := st281o2_p227
  have hstep := st281o2_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p229 : ((7157325527087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 228, stT281o2 (i+1)) + stT281o2 229 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 228
    simpa using h
  have hprev := st281o2_p228
  have hstep := st281o2_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p230 : ((414213332941/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 229, stT281o2 (i+1)) + stT281o2 230 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 229
    simpa using h
  have hprev := st281o2_p229
  have hstep := st281o2_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p231 : ((80225678957/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 230, stT281o2 (i+1)) + stT281o2 231 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 230
    simpa using h
  have hprev := st281o2_p230
  have hstep := st281o2_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p232 : ((1650357731503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 231, stT281o2 (i+1)) + stT281o2 232 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 231
    simpa using h
  have hprev := st281o2_p231
  have hstep := st281o2_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p233 : ((888676796237/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 232, stT281o2 (i+1)) + stT281o2 233 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 232
    simpa using h
  have hprev := st281o2_p232
  have hstep := st281o2_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p234 : ((485057758911/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 233, stT281o2 (i+1)) + stT281o2 234 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 233
    simpa using h
  have hprev := st281o2_p233
  have hstep := st281o2_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p235 : ((260243784017/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 234, stT281o2 (i+1)) + stT281o2 235 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 234
    simpa using h
  have hprev := st281o2_p234
  have hstep := st281o2_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p236 : ((269213121051/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 235, stT281o2 (i+1)) + stT281o2 236 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 235
    simpa using h
  have hprev := st281o2_p235
  have hstep := st281o2_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p237 : ((4262912118321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 236, stT281o2 (i+1)) + stT281o2 237 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 236
    simpa using h
  have hprev := st281o2_p236
  have hstep := st281o2_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p238 : ((161880488769/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 237, stT281o2 (i+1)) + stT281o2 238 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 237
    simpa using h
  have hprev := st281o2_p237
  have hstep := st281o2_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p239 : ((3733846418951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 238, stT281o2 (i+1)) + stT281o2 239 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 238
    simpa using h
  have hprev := st281o2_p238
  have hstep := st281o2_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p240 : ((1714453838509/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 239, stT281o2 (i+1)) + stT281o2 240 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 239
    simpa using h
  have hprev := st281o2_p239
  have hstep := st281o2_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p241 : ((3233286858473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 240, stT281o2 (i+1)) + stT281o2 241 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 240
    simpa using h
  have hprev := st281o2_p240
  have hstep := st281o2_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p242 : ((6421003209871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 241, stT281o2 (i+1)) + stT281o2 242 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 241
    simpa using h
  have hprev := st281o2_p241
  have hstep := st281o2_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p243 : ((6733284768371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 242, stT281o2 (i+1)) + stT281o2 243 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 242
    simpa using h
  have hprev := st281o2_p242
  have hstep := st281o2_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p244 : ((7299514712691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 243, stT281o2 (i+1)) + stT281o2 244 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 243
    simpa using h
  have hprev := st281o2_p243
  have hstep := st281o2_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p245 : ((7935811570279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 244, stT281o2 (i+1)) + stT281o2 245 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 244
    simpa using h
  have hprev := st281o2_p244
  have hstep := st281o2_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p246 : ((1687764283459/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 245, stT281o2 (i+1)) + stT281o2 246 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 245
    simpa using h
  have hprev := st281o2_p245
  have hstep := st281o2_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p247 : ((8650492743007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 246, stT281o2 (i+1)) + stT281o2 247 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 246
    simpa using h
  have hprev := st281o2_p246
  have hstep := st281o2_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p248 : ((1063328443931/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 247, stT281o2 (i+1)) + stT281o2 248 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 247
    simpa using h
  have hprev := st281o2_p247
  have hstep := st281o2_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p249 : ((503418781853/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 248, stT281o2 (i+1)) + stT281o2 249 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 248
    simpa using h
  have hprev := st281o2_p248
  have hstep := st281o2_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_p250 : ((232394066101/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT281o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT281o2 (i+1))
      = (∑ i ∈ Finset.range 249, stT281o2 (i+1)) + stT281o2 250 := by
    have h := Finset.sum_range_succ (fun i => stT281o2 (i+1)) 249
    simpa using h
  have hprev := st281o2_p249
  have hstep := st281o2_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st281o2_s250 :
    |Real.sin (((281 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))
      - ((42431/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log ((250 : ℕ)) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((250 : ℕ)) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact sinMulShift_eval (r := 1829883/2500000) (δ := 1427/200000000) (ψ := 2829/500000) 281 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 281/2`** (evaluated boundary). -/
theorem station_281o2_sign : hardyG (((((281:ℕ)):ℝ)/2)) < 0 := by
  have hcore := phase_station_lower_half_eval 281 250 (by norm_num) (by norm_num)
    ((2829/500000 : ℚ) : ℝ)
  have hchain := st281o2_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT281o2 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((281 : ℕ) : ℝ) * (Real.log ((i+1 : ℕ)) / 2)
              - ((2829/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st281o2_c250
  have hsinb := abs_le.mp st281o2_s250
  have hbdy_lo : ((-4636884288883/197405000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((281 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ))) / 2
          - ((((281:ℕ)):ℝ)/2)
            * Real.sin (((281 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((2829/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((281:ℕ)):ℝ)/2) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((281:ℝ) * (Real.log (250:ℝ) / 2) - ((2829/500000 : ℚ) : ℝ))) / 2
        - ((281:ℝ)/2) * Real.sin ((281:ℝ) * (Real.log (250:ℝ) / 2) - ((2829/500000 : ℚ) : ℝ))
        ≥ ((-58652419/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((281:ℝ)/2) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-58652419/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-58652419/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-58652419/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((281:ℕ)):ℝ)/2)+1) * (((((281:ℕ)):ℝ)/2)+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((229631412967/500000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((232394066101/312500000000 : ℚ) : ℝ) + ((-4636884288883/197405000000000 : ℚ) : ℝ)
      - ((229631412967/500000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((2829/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line (((((281:ℕ)):ℝ)/2)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((2829/500000 : ℚ) : ℝ)
        * (riemannZeta (line (((((281:ℕ)):ℝ)/2)))).re
      - Real.sin ((2829/500000 : ℚ) : ℝ)
        * (riemannZeta (line (((((281:ℕ)):ℝ)/2)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((((281:ℕ)):ℝ)/2))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((((281:ℕ)):ℝ)/2))
      = ((((((281:ℕ)):ℝ)/2)) * (Real.log (((((281:ℕ)):ℝ)/2)) - Real.log 2
          - Real.log Real.pi) - (((((281:ℕ)):ℝ)/2))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM : ((24726037/5000000 : ℚ) : ℝ) ≤ Real.log (((((281:ℕ)):ℝ)/2))
      ∧ Real.log (((((281:ℕ)):ℝ)/2)) ≤ ((12363019/2500000 : ℚ) : ℝ) := by
    have hsplit : Real.log (((((281:ℕ)):ℝ)/2))
        = Real.log ((((281:ℕ)):ℝ)) - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    have hM := log_br_281
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
  have hθwin : |(((2829/500000 : ℚ) : ℝ) + ((24:ℤ)) * (2*Real.pi) - Real.pi) - theta (((((281:ℕ)):ℝ)/2))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((((281:ℕ)):ℝ)/2)))
    (φ := ((2829/500000 : ℚ) : ℝ) + ((24:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((2829/500000 : ℚ) : ℝ) + ((24:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((2829/500000 : ℚ)) : ℝ) - Real.pi) + ((24:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((2829/500000 : ℚ)) : ℝ) - Real.pi) 24).1,
    (cos_sin_shift ((((2829/500000 : ℚ)) : ℝ) - Real.pi) 24).2]
  exact cos_sin_flip ((2829/500000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_281o2_sign
end AxiomAudit
