import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 122` (rung-126; evaluated boundary, N = 200)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT122 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((122 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((80867/500000 : ℚ) : ℝ))

theorem st122_c1 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((19739/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -80867/2000000) (δ := 1/100000000) (ψ := 80867/500000) 122 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t1 : ((9869/10000 : ℚ) : ℝ) ≤ stT122 1 := by
  have hc : ((9869/10000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9869/10000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((9869/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c2 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-912771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 425127/625000) (δ := 961/100000000) (ψ := 80867/500000) 122 13
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t2 : ((-1613654840707/2500000000000 : ℚ) : ℝ) ≤ stT122 2 := by
  have hc : ((-912821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1613654840707/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-912821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c3 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-344097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75081/156250) (δ := 1067/100000000) (ψ := 80867/500000) 122 21
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t3 : ((-1986933736941/10000000000000 : ℚ) : ℝ) ≤ stT122 3 := by
  have hc : ((-344147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1986933736941/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-344147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c4 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((388841/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -424891/2500000) (δ := 711/100000000) (ψ := 80867/500000) 122 27
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t4 : ((24301/62500 : ℚ) : ℝ) ≤ stT122 4 := by
  have hc : ((24301/31250 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24301/62500 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((24301/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c5 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((15917/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1763683/5000000) (δ := 1109/100000000) (ψ := 80867/500000) 122 31
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t5 : ((1779015303/25000000000 : ℚ) : ℝ) ≤ stT122 5 := by
  have hc : ((1989/12500 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1779015303/25000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((1989/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c6 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((92101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -924103/2500000) (δ := 817/100000000) (ψ := 80867/500000) 122 35
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t6 : ((187898275291/5000000000000 : ℚ) : ℝ) ≤ stT122 6 := by
  have hc : ((92051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187898275291/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((92051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c7 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((49039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -475543/1250000) (δ := 317/50000000) (ψ := 80867/500000) 122 38
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t7 : ((46290244979/2500000000000 : ℚ) : ℝ) ≤ stT122 7 := by
  have hc : ((48989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46290244979/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((48989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c8 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-590699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1376701/2500000) (δ := 733/100000000) (ψ := 80867/500000) 122 40
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t8 : ((-1044306587483/5000000000000 : ℚ) : ℝ) ≤ stT122 8 := by
  have hc : ((-590749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1044306587483/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-590749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c9 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-649181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -284663/500000) (δ := 461/50000000) (ψ := 80867/500000) 122 43
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t9 : ((-1082051883077/5000000000000 : ℚ) : ℝ) ≤ stT122 9 := by
  have hc : ((-649231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1082051883077/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-649231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c10 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-406751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4974229/10000000) (δ := 281/25000000) (ψ := 80867/500000) 122 45
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t10 : ((-643208926339/5000000000000 : ℚ) : ℝ) ≤ stT122 10 := by
  have hc : ((-406801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-643208926339/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-406801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c11 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-488661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7320551/10000000) (δ := 173/20000000) (ψ := 80867/500000) 122 47
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t11 : ((-368361000051/1250000000000 : ℚ) : ℝ) ≤ stT122 11 := by
  have hc : ((-244343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-368361000051/1250000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-244343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c12 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((166041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 877489/2500000) (δ := 627/100000000) (ψ := 80867/500000) 122 48
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t12 : ((479174685241/10000000000000 : ℚ) : ℝ) ≤ stT122 12 := by
  have hc : ((165991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((479174685241/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((165991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c13 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((172747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -698589/2000000) (δ := 677/100000000) (ψ := 80867/500000) 122 50
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t13 : ((957950259/20000000000 : ℚ) : ℝ) ≤ stT122 13 := by
  have hc : ((172697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((957950259/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((172697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c14 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((208447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3402023/10000000) (δ := 179/20000000) (ψ := 80867/500000) 122 51
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t14 : ((139241080741/2500000000000 : ℚ) : ℝ) ≤ stT122 14 := by
  have hc : ((208397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139241080741/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((208397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c15 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-234571/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6971077/10000000) (δ := 1213/100000000) (ψ := 80867/500000) 122 53
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t15 : ((-1211384033163/5000000000000 : ℚ) : ℝ) ≤ stT122 15 := by
  have hc : ((-469167/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1211384033163/5000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-469167/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c16 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((364299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -374349/1250000) (δ := 983/100000000) (ψ := 80867/500000) 122 54
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t16 : ((364249/4000000 : ℚ) : ℝ) ≤ stT122 16 := by
  have hc : ((364249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364249/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((364249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c17 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((498199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42449/2000000) (δ := 173/25000000) (ψ := 80867/500000) 122 55
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t17 : ((151031162493/625000000000 : ℚ) : ℝ) ≤ stT122 17 := by
  have hc : ((249087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151031162493/625000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((249087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c18 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((205591/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 378277/2500000) (δ := 351/50000000) (ψ := 80867/500000) 122 56
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t18 : ((484553047227/2500000000000 : ℚ) : ℝ) ≤ stT122 18 := by
  have hc : ((411157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((484553047227/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((411157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c19 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((121441/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2295647/10000000) (δ := 119/12500000) (ψ := 80867/500000) 122 57
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t19 : ((278581778667/2000000000000 : ℚ) : ℝ) ≤ stT122 19 := by
  have hc : ((121431/200000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((278581778667/2000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((121431/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c20 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((627191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1116069/5000000) (δ := 863/100000000) (ψ := 80867/500000) 122 58
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t20 : ((1402329294447/10000000000000 : ℚ) : ℝ) ≤ stT122 20 := by
  have hc : ((627141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1402329294447/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((627141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c21 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((423077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56207/400000) (δ := 789/100000000) (ψ := 80867/500000) 122 59
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t21 : ((115396845907/625000000000 : ℚ) : ℝ) ≤ stT122 21 := by
  have hc : ((105763/125000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115396845907/625000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((105763/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c22 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((998957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -114183/10000000) (δ := 129/20000000) (ψ := 80867/500000) 122 60
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t22 : ((2129676716349/10000000000000 : ℚ) : ℝ) ≤ stT122 22 := by
  have hc : ((998907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2129676716349/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((998907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c23 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((617101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2264359/10000000) (δ := 131/12500000) (ψ := 80867/500000) 122 61
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t23 : ((160830023793/1250000000000 : ℚ) : ℝ) ≤ stT122 23 := by
  have hc : ((617051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160830023793/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((617051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c24 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-25819/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -124791/250000) (δ := 877/100000000) (ψ := 80867/500000) 122 62
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t24 : ((-210836824317/2500000000000 : ℚ) : ℝ) ≤ stT122 24 := by
  have hc : ((-206577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-210836824317/2500000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-206577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c25 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-987549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1864767/2500000) (δ := 957/100000000) (ψ := 80867/500000) 122 62
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t25 : ((-1975198987599/10000000000000 : ℚ) : ℝ) ≤ stT122 25 := by
  have hc : ((-987599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1975198987599/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-987599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c26 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((85323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3713423/10000000) (δ := 383/50000000) (ψ := 80867/500000) 122 63
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t26 : ((167234081953/10000000000000 : ℚ) : ℝ) ≤ stT122 26 := by
  have hc : ((85273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167234081953/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((85273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c27 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((490669/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -483741/10000000) (δ := 767/100000000) (ψ := 80867/500000) 122 64
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t27 : ((472122189/2500000000 : ℚ) : ℝ) ≤ stT122 27 := by
  have hc : ((122661/125000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((472122189/2500000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((122661/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c28 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-452023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1274893/2500000) (δ := 221/20000000) (ψ := 80867/500000) 122 65
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t28 : ((-854337953079/10000000000000 : ℚ) : ℝ) ≤ stT122 28 := by
  have hc : ((-452073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-854337953079/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-452073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c29 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-62139/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70041/125000) (δ := 177/20000000) (ψ := 80867/500000) 122 65
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t29 : ((-901551167/7812500000 : ℚ) : ℝ) ≤ stT122 29 := by
  have hc : ((-1942/3125 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-901551167/7812500000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-1942/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c30 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((497787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23529/1000000) (δ := 969/100000000) (ψ := 80867/500000) 122 66
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t30 : ((454392245821/2500000000000 : ℚ) : ℝ) ≤ stT122 30 := by
  have hc : ((248881/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454392245821/2500000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((248881/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c31 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-579337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5471777/10000000) (δ := 1183/100000000) (ψ := 80867/500000) 122 67
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t31 : ((-520305169449/5000000000000 : ℚ) : ℝ) ≤ stT122 31 := by
  have hc : ((-579387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-520305169449/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-579387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c32 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-28397/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 526447/1250000) (δ := 1203/100000000) (ψ := 80867/500000) 122 67
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t32 : ((-100442753173/5000000000000 : ℚ) : ℝ) ≤ stT122 32 := by
  have hc : ((-56819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100442753173/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-56819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c33 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((664171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2111031/10000000) (δ := 3/400000) (ψ := 80867/500000) 122 68
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t33 : ((144510737237/1250000000000 : ℚ) : ℝ) ≤ stT122 33 := by
  have hc : ((664121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144510737237/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((664121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c34 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-117679/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3497061/5000000) (δ := 953/100000000) (ψ := 80867/500000) 122 68
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t34 : ((-403657112313/2500000000000 : ℚ) : ℝ) ≤ stT122 34 := by
  have hc : ((-470741/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-403657112313/2500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-470741/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c35 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((998703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 63679/5000000) (δ := 741/100000000) (ψ := 80867/500000) 122 69
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t35 : ((422007788781/2500000000000 : ℚ) : ℝ) ≤ stT122 35 := by
  have hc : ((998653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((422007788781/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((998653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c36 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-94067/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -873561/1250000) (δ := 771/100000000) (ψ := 80867/500000) 122 70
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t36 : ((-19598337253/125000000000 : ℚ) : ℝ) ≤ stT122 36 := by
  have hc : ((-11759/12500 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19598337253/125000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-11759/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c37 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((853943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1368199/10000000) (δ := 1091/100000000) (ψ := 80867/500000) 122 70
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t37 : ((1403790699177/10000000000000 : ℚ) : ℝ) ≤ stT122 37 := by
  have hc : ((853893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1403790699177/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((853893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c38 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-395237/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6205949/10000000) (δ := 351/50000000) (ψ := 80867/500000) 122 71
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t38 : ((-64119994533/500000000000 : ℚ) : ℝ) ≤ stT122 38 := by
  have hc : ((-197631/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64119994533/500000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-197631/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c39 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((773387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 68663/400000) (δ := 661/100000000) (ψ := 80867/500000) 122 71
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t39 : ((1238329844697/10000000000000 : ℚ) : ℝ) ≤ stT122 39 := by
  have hc : ((773337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1238329844697/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((773337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c40 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-805777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6269457/10000000) (δ := 653/100000000) (ψ := 80867/500000) 122 72
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t40 : ((-1274124496953/10000000000000 : ℚ) : ℝ) ≤ stT122 40 := by
  have hc : ((-805827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1274124496953/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-805827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c41 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((54707/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126179/1000000) (δ := 813/100000000) (ψ := 80867/500000) 122 72
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t41 : ((683464525047/5000000000000 : ℚ) : ℝ) ≤ stT122 41 := by
  have hc : ((437631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((683464525047/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((437631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c42 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-477219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -354821/500000) (δ := 999/100000000) (ψ := 80867/500000) 122 73
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t42 : ((-92050464787/625000000000 : ℚ) : ℝ) ≤ stT122 42 := by
  have hc : ((-119311/125000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92050464787/625000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-119311/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c43 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((999483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80381/10000000) (δ := 1059/100000000) (ψ := 80867/500000) 122 73
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t43 : ((304824066701/2000000000000 : ℚ) : ℝ) ≤ stT122 43 := by
  have hc : ((999433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((304824066701/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((999433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c44 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-953931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 886523/1250000) (δ := 839/100000000) (ψ := 80867/500000) 122 73
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t44 : ((-1438180734417/10000000000000 : ℚ) : ℝ) ≤ stT122 44 := by
  have hc : ((-953981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1438180734417/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-953981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c45 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((11904/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -880779/5000000) (δ := 43/4000000) (ψ := 80867/500000) 122 74
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t45 : ((567816292033/5000000000000 : ℚ) : ℝ) ≤ stT122 45 := by
  have hc : ((380903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((567816292033/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((380903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c46 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-6171/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4942009/10000000) (δ := 47/4000000) (ψ := 80867/500000) 122 74
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t46 : ((-14559676337/250000000000 : ℚ) : ℝ) ≤ stT122 46 := by
  have hc : ((-197497/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14559676337/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-197497/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c47 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-27899/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2103281/5000000) (δ := 609/50000000) (ψ := 80867/500000) 122 75
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t47 : ((-1628524379/100000000000 : ℚ) : ℝ) ≤ stT122 47 := by
  have hc : ((-55823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1628524379/100000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-55823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c48 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((3163/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 276841/1250000) (δ := 549/50000000) (ψ := 80867/500000) 122 75
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t48 : ((146081097/1600000000 : ℚ) : ℝ) ≤ stT122 48 := by
  have hc : ((12651/20000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146081097/1600000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((12651/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c49 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-241607/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7204353/10000000) (δ := 147/12500000) (ψ := 80867/500000) 122 76
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t49 : ((-172585426177/1250000000000 : ℚ) : ℝ) ≤ stT122 49 := by
  have hc : ((-483239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172585426177/1250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-483239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c50 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((14286/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1042527/10000000) (δ := 1167/100000000) (ψ := 80867/500000) 122 76
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t50 : ((646474946051/5000000000000 : ℚ) : ℝ) ≤ stT122 50 := by
  have hc : ((457127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((646474946051/5000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((457127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c51 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-83031/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2498637/5000000) (δ := 847/100000000) (ψ := 80867/500000) 122 76
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t51 : ((-116280734521/2000000000000 : ℚ) : ℝ) ≤ stT122 51 := by
  have hc : ((-83041/200000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116280734521/2000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-83041/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c52 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-337701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4788173/10000000) (δ := 127/12500000) (ψ := 80867/500000) 122 77
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t52 : ((-468376537001/10000000000000 : ℚ) : ℝ) ≤ stT122 52 := by
  have hc : ((-337751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-468376537001/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-337751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c53 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((458837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1021527/10000000) (δ := 33/3125000) (ψ := 80867/500000) 122 77
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t53 : ((31511322863/250000000000 : ℚ) : ℝ) ≤ stT122 53 := by
  have hc : ((114703/125000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31511322863/250000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((114703/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c54 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-899339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6722627/10000000) (δ := 169/25000000) (ψ := 80867/500000) 122 77
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t54 : ((-305978433523/2500000000000 : ℚ) : ℝ) ≤ stT122 54 := by
  have hc : ((-899389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305978433523/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-899389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c55 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((106799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3388849/10000000) (δ := 509/50000000) (ψ := 80867/500000) 122 78
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t55 : ((71986977413/2500000000000 : ℚ) : ℝ) ≤ stT122 55 := by
  have hc : ((53387/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71986977413/2500000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((53387/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c56 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((166359/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 421359/2000000) (δ := 539/50000000) (ψ := 80867/500000) 122 78
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t56 : ((222289826029/2500000000000 : ℚ) : ℝ) ≤ stT122 56 := by
  have hc : ((332693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222289826029/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((332693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c57 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-495141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3752583/5000000) (δ := 399/50000000) (ψ := 80867/500000) 122 78
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t57 : ((-327931853739/2500000000000 : ℚ) : ℝ) ≤ stT122 57 := by
  have hc : ((-247583/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-327931853739/2500000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-247583/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c58 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((399957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -579663/2000000) (δ := 219/20000000) (ψ := 80867/500000) 122 79
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t58 : ((65637935631/1250000000000 : ℚ) : ℝ) ≤ stT122 58 := by
  have hc : ((399907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65637935631/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((399907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c59 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((7511/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2315487/10000000) (δ := 139/20000000) (ψ := 80867/500000) 122 79
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t59 : ((78221396787/1000000000000 : ℚ) : ℝ) ≤ stT122 59 := by
  have hc : ((60083/100000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78221396787/1000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((60083/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c60 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-98643/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3720829/5000000) (δ := 187/25000000) (ψ := 80867/500000) 122 79
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t60 : ((-3183851869/25000000000 : ℚ) : ℝ) ≤ stT122 60 := by
  have hc : ((-12331/12500 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3183851869/25000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-12331/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c61 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((69293/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -806217/2500000) (δ := 779/100000000) (ψ := 80867/500000) 122 80
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t61 : ((11088066903/312500000000 : ℚ) : ℝ) ≤ stT122 61 := by
  have hc : ((138561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11088066903/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((138561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c62 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((384399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1734591/10000000) (δ := 1039/100000000) (ψ := 80867/500000) 122 80
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t62 : ((244077682187/2500000000000 : ℚ) : ℝ) ≤ stT122 62 := by
  have hc : ((192187/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((244077682187/2500000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((192187/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c63 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-879629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1322939/2000000) (δ := 113/12500000) (ψ := 80867/500000) 122 80
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t63 : ((-554145868939/5000000000000 : ℚ) : ℝ) ≤ stT122 63 := by
  have hc : ((-879679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-554145868939/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-879679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c64 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-72351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -214501/500000) (δ := 99/10000000) (ψ := 80867/500000) 122 81
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t64 : ((-11308759047/625000000000 : ℚ) : ℝ) ≤ stT122 64 := by
  have hc : ((-9047/62500 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11308759047/625000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-9047/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c65 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((984639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 438757/10000000) (δ := 83/10000000) (ψ := 80867/500000) 122 81
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t65 : ((1221232012383/10000000000000 : ℚ) : ℝ) ≤ stT122 65 := by
  have hc : ((984589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1221232012383/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((984589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c66 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-450511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 636917/1250000) (δ := 733/100000000) (ψ := 80867/500000) 122 81
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t66 : ((-110920458663/2000000000000 : ℚ) : ℝ) ≤ stT122 66 := by
  have hc : ((-450561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110920458663/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-450561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c67 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-744399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241043/400000) (δ := 1023/100000000) (ψ := 80867/500000) 122 82
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t67 : ((-181897924211/2000000000000 : ℚ) : ℝ) ≤ stT122 67 := by
  have hc : ((-744449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181897924211/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-744449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c68 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((205911/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1507473/10000000) (δ := 1163/100000000) (ψ := 80867/500000) 122 82
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t68 : ((249688581183/2500000000000 : ℚ) : ℝ) ≤ stT122 68 := by
  have hc : ((411797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249688581183/2500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((411797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c69 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((191357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73629/250000) (δ := 1203/100000000) (ψ := 80867/500000) 122 82
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t69 : ((28792069857/625000000000 : ℚ) : ℝ) ≤ stT122 69 := by
  have hc : ((47833/125000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28792069857/625000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((47833/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c70 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-39137/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 293349/400000) (δ := 743/100000000) (ψ := 80867/500000) 122 82
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t70 : ((-46780067831/400000000000 : ℚ) : ℝ) ≤ stT122 70 := by
  have hc : ((-39139/40000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46780067831/400000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-39139/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c71 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-24177/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1011981/2500000) (δ := 931/100000000) (ψ := 80867/500000) 122 83
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t71 : ((-7180624491/1250000000000 : ℚ) : ℝ) ≤ stT122 71 := by
  have hc : ((-12101/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7180624491/1250000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-12101/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c72 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((199241/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5447/250000) (δ := 31/3125000) (ψ := 80867/500000) 122 83
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t72 : ((234795925041/2000000000000 : ℚ) : ℝ) ≤ stT122 72 := by
  have hc : ((199231/200000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234795925041/2000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((199231/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c73 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-197827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4424843/10000000) (δ := 183/25000000) (ψ := 80867/500000) 122 83
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t73 : ((-57899403831/2500000000000 : ℚ) : ℝ) ≤ stT122 73 := by
  have hc : ((-197877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57899403831/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-197877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c74 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-958747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7133397/10000000) (δ := 551/50000000) (ψ := 80867/500000) 122 84
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t74 : ((-1114579460169/10000000000000 : ℚ) : ℝ) ≤ stT122 74 := by
  have hc : ((-958797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1114579460169/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-958797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c75 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((173817/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4863/16000) (δ := 1061/100000000) (ψ := 80867/500000) 122 84
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t75 : ((62711757/1562500000 : ℚ) : ℝ) ≤ stT122 75 := by
  have hc : ((5431/15625 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62711757/1562500000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((5431/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c76 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((230249/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1000419/10000000) (δ := 741/100000000) (ψ := 80867/500000) 122 84
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t76 : ((264099223947/2500000000000 : ℚ) : ℝ) ≤ stT122 76 := by
  have hc : ((460473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264099223947/2500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((460473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c77 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-10289/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1246851/2500000) (δ := 961/100000000) (ψ := 80867/500000) 122 84
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t77 : ((-23453661283/500000000000 : ℚ) : ℝ) ≤ stT122 77 := by
  have hc : ((-41161/100000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23453661283/500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-41161/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c78 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-90997/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6785021/10000000) (δ := 91/10000000) (ψ := 80867/500000) 122 85
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t78 : ((-25759890639/250000000000 : ℚ) : ℝ) ≤ stT122 78 := by
  have hc : ((-45501/50000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25759890639/250000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-45501/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c79 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((9987/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1449809/5000000) (δ := 633/100000000) (ψ := 80867/500000) 122 85
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t79 : ((44939350041/1000000000000 : ℚ) : ℝ) ≤ stT122 79 := by
  have hc : ((39943/100000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44939350041/1000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((39943/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c80 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((465297/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 93691/1000000) (δ := 83/10000000) (ψ := 80867/500000) 122 85
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t80 : ((65023681247/625000000000 : ℚ) : ℝ) ≤ stT122 80 := by
  have hc : ((58159/62500 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65023681247/625000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((58159/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c81 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-157053/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4725779/10000000) (δ := 653/100000000) (ψ := 80867/500000) 122 85
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t81 : ((-10908203171/312500000000 : ℚ) : ℝ) ≤ stT122 81 := by
  have hc : ((-78539/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10908203171/312500000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-78539/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c82 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-38799/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3619903/5000000) (δ := 33/5000000) (ψ := 80867/500000) 122 86
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t82 : ((-10712141279/100000000000 : ℚ) : ℝ) ≤ stT122 82 := by
  have hc : ((-38801/40000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10712141279/100000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-38801/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c83 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((38269/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3542791/10000000) (δ := 57/5000000) (ψ := 80867/500000) 122 86
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t83 : ((41991941173/2500000000000 : ℚ) : ℝ) ≤ stT122 83 := by
  have hc : ((76513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41991941173/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((76513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c84 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((999033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109947/10000000) (δ := 63/5000000) (ψ := 80867/500000) 122 86
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t84 : ((1089979362487/10000000000000 : ℚ) : ℝ) ≤ stT122 84 := by
  have hc : ((998983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1089979362487/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((998983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c85 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((41459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3719457/10000000) (δ := 683/100000000) (ψ := 80867/500000) 122 86
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t85 : ((5617683871/625000000000 : ℚ) : ℝ) ≤ stT122 85 := by
  have hc : ((20717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5617683871/625000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((20717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c86 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-97437/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7286749/10000000) (δ := 1163/100000000) (ψ := 80867/500000) 122 86
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t86 : ((-6567152311/62500000000 : ℚ) : ℝ) ≤ stT122 86 := by
  have hc : ((-48721/50000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6567152311/62500000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-48721/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c87 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-377661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1223791/2500000) (δ := 1029/100000000) (ψ := 80867/500000) 122 87
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t87 : ((-404948873343/10000000000000 : ℚ) : ℝ) ≤ stT122 87 := by
  have hc : ((-377711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-404948873343/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-377711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c88 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((3381/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1409411/10000000) (δ := 1049/100000000) (ψ := 80867/500000) 122 87
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t88 : ((2252464339/25000000000 : ℚ) : ℝ) ≤ stT122 88 := by
  have hc : ((2113/2500 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2252464339/25000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((2113/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c89 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((171507/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2036953/10000000) (δ := 417/50000000) (ψ := 80867/500000) 122 87
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t89 : ((363567311033/5000000000000 : ℚ) : ℝ) ≤ stT122 89 := by
  have hc : ((342989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((363567311033/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((342989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c90 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-570511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 544481/1000000) (δ := 427/50000000) (ψ := 80867/500000) 122 87
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t90 : ((-601424356173/10000000000000 : ℚ) : ℝ) ≤ stT122 90 := by
  have hc : ((-570561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-601424356173/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-570561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c91 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-927019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3446477/5000000) (δ := 253/20000000) (ψ := 80867/500000) 122 88
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t91 : ((-194366505333/2000000000000 : ℚ) : ℝ) ≤ stT122 91 := by
  have hc : ((-927069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194366505333/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-927069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c92 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((146433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3559587/10000000) (δ := 37/4000000) (ψ := 80867/500000) 122 88
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t92 : ((38153704269/2500000000000 : ℚ) : ℝ) ≤ stT122 92 := by
  have hc : ((146383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38153704269/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((146383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c93 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((994503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131129/5000000) (δ := 221/20000000) (ψ := 80867/500000) 122 88
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t93 : ((1031199032803/10000000000000 : ℚ) : ℝ) ≤ stT122 93 := by
  have hc : ((994453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1031199032803/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((994453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c94 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((36243/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1499903/5000000) (δ := 201/20000000) (ψ := 80867/500000) 122 88
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t94 : ((18688317099/500000000000 : ℚ) : ℝ) ≤ stT122 94 := by
  have hc : ((18119/50000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18688317099/500000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((18119/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c95 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-99461/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6227349/10000000) (δ := 221/20000000) (ψ := 80867/500000) 122 88
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t95 : ((-408205238751/5000000000000 : ℚ) : ℝ) ≤ stT122 95 := by
  have hc : ((-397869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-408205238751/5000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-397869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c96 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-404941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1571717/2500000) (δ := 219/20000000) (ψ := 80867/500000) 122 89
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t96 : ((-206658401943/2500000000000 : ℚ) : ℝ) ≤ stT122 96 := by
  have hc : ((-202483/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206658401943/2500000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-202483/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c97 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((15743/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1563109/5000000) (δ := 187/20000000) (ψ := 80867/500000) 122 89
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t97 : ((15982053713/500000000000 : ℚ) : ℝ) ≤ stT122 97 := by
  have hc : ((31481/100000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15982053713/500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((31481/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c98 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 403/2000000) (δ := 191/20000000) (ψ := 80867/500000) 122 89
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t98 : ((2525253731/25000000000 : ℚ) : ℝ) ≤ stT122 98 := by
  have hc : ((19999/20000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2525253731/25000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((19999/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c99 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((40671/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 387311/1250000) (δ := 157/25000000) (ψ := 80867/500000) 122 89
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t99 : ((163478313383/5000000000000 : ℚ) : ℝ) ≤ stT122 99 := by
  have hc : ((162659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163478313383/5000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((162659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c100 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-390023/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9631/15625) (δ := 203/20000000) (ψ := 80867/500000) 122 89
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t100 : ((-12189/156250 : ℚ) : ℝ) ≤ stT122 100 := by
  have hc : ((-12189/15625 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12189/156250 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-12189/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c101 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-171759/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -813659/1250000) (δ := 1037/100000000) (ψ := 80867/500000) 122 90
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t101 : ((-85458341111/1000000000000 : ℚ) : ℝ) ≤ stT122 101 := by
  have hc : ((-171769/200000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85458341111/1000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-171769/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c102 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((168263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1752161/5000000) (δ := 1097/100000000) (ψ := 80867/500000) 122 90
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t102 : ((166555597311/10000000000000 : ℚ) : ℝ) ≤ stT122 102 := by
  have hc : ((168213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166555597311/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((168213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c103 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((488861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33043/625000) (δ := 533/50000000) (ψ := 80867/500000) 122 90
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t103 : ((120416071761/1250000000000 : ℚ) : ℝ) ≤ stT122 103 := by
  have hc : ((122209/125000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120416071761/1250000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((122209/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c104 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((567543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 483639/2000000) (δ := 603/50000000) (ψ := 80867/500000) 122 90
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t104 : ((27823614297/500000000000 : ℚ) : ℝ) ≤ stT122 104 := by
  have hc : ((567493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27823614297/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((567493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c105 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-133633/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5336877/10000000) (δ := 637/100000000) (ψ := 80867/500000) 122 90
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t105 : ((-260849554191/5000000000000 : ℚ) : ℝ) ≤ stT122 105 := by
  have hc : ((-267291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260849554191/5000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-267291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c106 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-247209/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7480069/10000000) (δ := 1137/100000000) (ψ := 80867/500000) 122 91
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t106 : ((-240122781849/2500000000000 : ℚ) : ℝ) ≤ stT122 106 := by
  have hc : ((-494443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240122781849/2500000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-494443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c107 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-68051/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2308099/5000000) (δ := 403/50000000) (ψ := 80867/500000) 122 91
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t107 : ((-131599007599/5000000000000 : ℚ) : ℝ) ≤ stT122 107 := by
  have hc : ((-136127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131599007599/5000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-136127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c108 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((378663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1778969/10000000) (δ := 463/50000000) (ψ := 80867/500000) 122 91
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t108 : ((728688831/10000000000 : ℚ) : ℝ) ≤ stT122 108 := by
  have hc : ((189319/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((728688831/10000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((189319/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c109 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((915983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1032111/10000000) (δ := 977/100000000) (ψ := 80867/500000) 122 91
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t109 : ((438652220829/5000000000000 : ℚ) : ℝ) ≤ stT122 109 := by
  have hc : ((915933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((438652220829/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((915933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c110 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((1751/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3817519/10000000) (δ := 797/100000000) (ψ := 80867/500000) 122 91
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t110 : ((833802519/200000000000 : ℚ) : ℝ) ≤ stT122 110 := by
  have hc : ((1749/40000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((833802519/200000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((1749/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c111 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-436249/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6577719/10000000) (δ := 603/50000000) (ψ := 80867/500000) 122 91
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t111 : ((-103523239323/1250000000000 : ℚ) : ℝ) ≤ stT122 111 := by
  have hc : ((-218137/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103523239323/1250000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-218137/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c112 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-208611/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15987/25000) (δ := 217/25000000) (ψ := 80867/500000) 122 92
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t112 : ((-24641356079/312500000000 : ℚ) : ℝ) ≤ stT122 112 := by
  have hc : ((-417247/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24641356079/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-417247/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c113 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((48587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3683671/10000000) (δ := 199/20000000) (ψ := 80867/500000) 122 92
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t113 : ((285520279/31250000000 : ℚ) : ℝ) ≤ stT122 113 := by
  have hc : ((24281/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285520279/31250000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((24281/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c114 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((57601/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -996429/10000000) (δ := 127/20000000) (ψ := 80867/500000) 122 92
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t114 : ((86312489211/1000000000000 : ℚ) : ℝ) ≤ stT122 114 := by
  have hc : ((460783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86312489211/1000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((460783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c115 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((19643/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1667343/10000000) (δ := 179/20000000) (ψ := 80867/500000) 122 92
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t115 : ((9158005221/125000000000 : ℚ) : ℝ) ≤ stT122 115 := by
  have hc : ((78567/100000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9158005221/125000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((78567/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c116 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-30367/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1077013/2500000) (δ := 17/1562500) (ψ := 80867/500000) 122 92
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t116 : ((-28204345829/2000000000000 : ℚ) : ℝ) ≤ stT122 116 := by
  have hc : ((-30377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28204345829/2000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-30377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c117 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-931909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3463047/5000000) (δ := 163/20000000) (ψ := 80867/500000) 122 92
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t117 : ((-861597027459/10000000000000 : ℚ) : ℝ) ≤ stT122 117 := by
  have hc : ((-931959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-861597027459/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-931959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c118 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-785589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6186109/10000000) (δ := 189/20000000) (ψ := 80867/500000) 122 93
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t118 : ((-28929584897/400000000000 : ℚ) : ℝ) ≤ stT122 118 := by
  have hc : ((-785639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28929584897/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-785639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c119 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((62781/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1806127/5000000) (δ := 559/50000000) (ψ := 80867/500000) 122 93
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t119 : ((7191037461/625000000000 : ℚ) : ℝ) ≤ stT122 119 := by
  have hc : ((15689/125000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7191037461/625000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((15689/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c120 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((911461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -529969/5000000) (δ := 29/4000000) (ψ := 80867/500000) 122 93
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t120 : ((83199975957/1000000000000 : ℚ) : ℝ) ≤ stT122 120 := by
  have hc : ((911411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83199975957/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((911411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c121 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((415893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1471197/10000000) (δ := 137/20000000) (ψ := 80867/500000) 122 93
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t121 : ((9451536003/125000000000 : ℚ) : ℝ) ≤ stT122 121 := by
  have hc : ((103967/125000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9451536003/125000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((103967/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c122 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-10901/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3981499/10000000) (δ := 141/20000000) (ψ := 80867/500000) 122 93
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t122 : ((-2472985377/1250000000000 : ℚ) : ℝ) ≤ stT122 122 := by
  have hc : ((-5463/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2472985377/1250000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-5463/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c123 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-212729/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6471309/10000000) (δ := 329/50000000) (ψ := 80867/500000) 122 93
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t123 : ((-38364525661/500000000000 : ℚ) : ℝ) ≤ stT122 123 := by
  have hc : ((-425483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38364525661/500000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-425483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c124 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-453479/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1353401/2000000) (δ := 789/100000000) (ψ := 80867/500000) 122 94
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t124 : ((-3181709661/39062500000 : ℚ) : ℝ) ≤ stT122 124 := by
  have hc : ((-14172/15625 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3181709661/39062500000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-14172/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c125 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-19431/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4317193/10000000) (δ := 397/50000000) (ψ := 80867/500000) 122 94
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t125 : ((-17385220643/1250000000000 : ℚ) : ℝ) ≤ stT122 125 := by
  have hc : ((-77749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17385220643/1250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-77749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c126 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((182109/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1886901/10000000) (δ := 577/50000000) (ψ := 80867/500000) 122 94
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t126 : ((32444861791/500000000000 : ℚ) : ℝ) ≤ stT122 126 := by
  have hc : ((364193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32444861791/500000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((364193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c127 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((978099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 524179/10000000) (δ := 1049/100000000) (ψ := 80867/500000) 122 94
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t127 : ((216969412111/2500000000000 : ℚ) : ℝ) ≤ stT122 127 := by
  have hc : ((978049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216969412111/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((978049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c128 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((49167/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 729087/2500000) (δ := 769/100000000) (ψ := 80867/500000) 122 94
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t128 : ((173809404769/5000000000000 : ℚ) : ℝ) ≤ stT122 128 := by
  have hc : ((196643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173809404769/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((196643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c129 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-259279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5289901/10000000) (δ := 587/50000000) (ψ := 80867/500000) 122 94
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t129 : ((-28538058263/625000000000 : ℚ) : ℝ) ≤ stT122 129 := by
  have hc : ((-32413/62500 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28538058263/625000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-32413/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c130 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-31141/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61161/80000) (δ := 307/50000000) (ψ := 80867/500000) 122 94
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t130 : ((-437021835579/5000000000000 : ℚ) : ℝ) ≤ stT122 130 := by
  have hc : ((-498281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-437021835579/5000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-498281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c131 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-131797/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2862831/5000000) (δ := 943/100000000) (ψ := 80867/500000) 122 95
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t131 : ((-23032086987/400000000000 : ℚ) : ℝ) ≤ stT122 131 := by
  have hc : ((-131807/200000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23032086987/400000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-131807/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c132 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((206789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -170313/500000) (δ := 983/100000000) (ψ := 80867/500000) 122 95
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t132 : ((44985786183/2500000000000 : ℚ) : ℝ) ≤ stT122 132 := by
  have hc : ((206739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44985786183/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((206739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c133 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((904007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -552181/5000000) (δ := 903/100000000) (ψ := 80867/500000) 122 95
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t133 : ((783829250313/10000000000000 : ℚ) : ℝ) ≤ stT122 133 := by
  have hc : ((903957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((783829250313/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((903957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c134 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((890607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1180293/10000000) (δ := 1243/100000000) (ψ := 80867/500000) 122 95
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t134 : ((192330923619/2500000000000 : ℚ) : ℝ) ≤ stT122 134 := by
  have hc : ((890557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192330923619/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((890557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c135 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((95221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3447961/10000000) (δ := 23/2500000) (ψ := 80867/500000) 122 95
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t135 : ((10241447469/625000000000 : ℚ) : ℝ) ≤ stT122 135 := by
  have hc : ((23799/125000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10241447469/625000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((23799/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c136 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-325447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2849447/5000000) (δ := 51/5000000) (ψ := 80867/500000) 122 95
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t136 : ((-8721561303/156250000000 : ℚ) : ℝ) ≤ stT122 136 := by
  have hc : ((-10171/15625 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8721561303/156250000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-10171/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c137 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-124937/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7774627/10000000) (δ := 933/100000000) (ψ := 80867/500000) 122 96
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t137 : ((-213492530367/2500000000000 : ℚ) : ℝ) ≤ stT122 137 := by
  have hc : ((-499773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213492530367/2500000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-499773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c138 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-606601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1111287/2000000) (δ := 103/10000000) (ψ := 80867/500000) 122 96
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t138 : ((-516415910307/10000000000000 : ℚ) : ℝ) ≤ stT122 138 := by
  have hc : ((-606651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-516415910307/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-606651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c139 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((113547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -167713/500000) (δ := 853/100000000) (ψ := 80867/500000) 122 96
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t139 : ((12035999767/625000000000 : ℚ) : ℝ) ≤ stT122 139 := by
  have hc : ((56761/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12035999767/625000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((56761/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c140 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((111607/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -116787/1000000) (δ := 953/100000000) (ψ := 80867/500000) 122 96
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t140 : ((188639640531/2500000000000 : ℚ) : ℝ) ≤ stT122 140 := by
  have hc : ((446403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188639640531/2500000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((446403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c141 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((4603/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1002957/10000000) (δ := 107/10000000) (ψ := 80867/500000) 122 96
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t141 : ((15504842061/200000000000 : ℚ) : ℝ) ≤ stT122 141 := by
  have hc : ((18411/20000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15504842061/200000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((18411/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c142 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((1513/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3158443/10000000) (δ := 67/10000000) (ψ := 80867/500000) 122 96
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t142 : ((5077884231/200000000000 : ℚ) : ℝ) ≤ stT122 142 := by
  have hc : ((6051/20000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5077884231/200000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((6051/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c143 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-326/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5298803/10000000) (δ := 873/100000000) (ψ := 80867/500000) 122 96
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t143 : ((-8724523219/200000000000 : ℚ) : ℝ) ≤ stT122 143 := by
  have hc : ((-10433/20000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8724523219/200000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-10433/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c144 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-985263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7424247/10000000) (δ := 119/10000000) (ψ := 80867/500000) 122 96
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t144 : ((-410547411771/5000000000000 : ℚ) : ℝ) ≤ stT122 144 := by
  have hc : ((-985313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-410547411771/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-985313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c145 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-782329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6172981/10000000) (δ := 361/50000000) (ψ := 80867/500000) 122 97
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t145 : ((-129946110489/2000000000000 : ℚ) : ℝ) ≤ stT122 145 := by
  have hc : ((-782379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129946110489/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-782379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c146 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-59869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4076753/10000000) (δ := 491/50000000) (ψ := 80867/500000) 122 97
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t146 : ((-24794661957/5000000000000 : ℚ) : ℝ) ≤ stT122 146 := by
  have hc : ((-59919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24794661957/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-59919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c147 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((174547/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -997417/5000000) (δ := 1021/100000000) (ψ := 80867/500000) 122 97
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t147 : ((143953612117/2500000000000 : ℚ) : ℝ) ≤ stT122 147 := by
  have hc : ((349069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143953612117/2500000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((349069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c148 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((499787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72971/10000000) (δ := 881/100000000) (ψ := 80867/500000) 122 97
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t148 : ((102700341357/1250000000000 : ℚ) : ℝ) ≤ stT122 148 := by
  have hc : ((249881/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102700341357/1250000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((249881/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c149 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((659427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2126851/10000000) (δ := 581/50000000) (ψ := 80867/500000) 122 97
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t149 : ((540182079087/10000000000000 : ℚ) : ℝ) ≤ stT122 149 := by
  have hc : ((659377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((540182079087/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((659377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c150 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-95853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 260437/625000) (δ := 1121/100000000) (ψ := 80867/500000) 122 97
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t150 : ((-78304511791/10000000000000 : ℚ) : ℝ) ≤ stT122 150 := by
  have hc : ((-95903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78304511791/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-95903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c151 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-393717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3096789/5000000) (δ := 391/50000000) (ψ := 80867/500000) 122 97
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t151 : ((-160211454219/2500000000000 : ℚ) : ℝ) ≤ stT122 151 := by
  have hc : ((-196871/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160211454219/2500000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-196871/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c152 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-990059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7501177/10000000) (δ := 991/100000000) (ψ := 80867/500000) 122 98
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t152 : ((-200771332693/2500000000000 : ℚ) : ℝ) ≤ stT122 152 := by
  have hc : ((-990109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200771332693/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-990109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c153 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-588879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -550117/1000000) (δ := 991/100000000) (ψ := 80867/500000) 122 98
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t153 : ((-476121416837/10000000000000 : ℚ) : ℝ) ≤ stT122 153 := by
  have hc : ((-588929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-476121416837/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-588929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c154 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((16437/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -219637/625000) (δ := 1211/100000000) (ψ := 80867/500000) 122 98
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t154 : ((413789597/31250000000 : ℚ) : ℝ) ≤ stT122 154 := by
  have hc : ((1027/6250 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((413789597/31250000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((1027/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c155 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((816179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61603/400000) (δ := 1031/100000000) (ψ := 80867/500000) 122 98
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t155 : ((655530319251/10000000000000 : ℚ) : ℝ) ≤ stT122 155 := by
  have hc : ((816129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((655530319251/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((816129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c156 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((985831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 210673/5000000) (δ := 1171/100000000) (ψ := 80867/500000) 122 98
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t156 : ((1233212031/15625000000 : ℚ) : ℝ) ≤ stT122 156 := by
  have hc : ((985781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1233212031/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((985781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c157 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((9113/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 474047/2000000) (δ := 1171/100000000) (ψ := 80867/500000) 122 98
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t157 : ((116357347413/2500000000000 : ℚ) : ℝ) ≤ stT122 157 := by
  have hc : ((291591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116357347413/2500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((291591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c158 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-3783/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4306749/10000000) (δ := 851/100000000) (ψ := 80867/500000) 122 98
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t158 : ((-6021180723/500000000000 : ℚ) : ℝ) ≤ stT122 158 := by
  have hc : ((-15137/100000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6021180723/500000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-15137/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c159 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-796583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3115523/5000000) (δ := 1211/100000000) (ψ := 80867/500000) 122 98
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t159 : ((-157942848479/2500000000000 : ℚ) : ℝ) ≤ stT122 159 := by
  have hc : ((-796633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157942848479/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-796633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c160 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-31041/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1512937/2000000) (δ := 13/1250000) (ψ := 80867/500000) 122 99
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t160 : ((-39266109817/500000000000 : ℚ) : ℝ) ≤ stT122 160 := by
  have hc : ((-496681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39266109817/500000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-496681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c161 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-160087/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -354023/625000) (δ := 763/100000000) (ψ := 80867/500000) 122 99
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t161 : ((-252352354089/5000000000000 : ℚ) : ℝ) ≤ stT122 161 := by
  have hc : ((-320199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252352354089/5000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-320199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c162 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((60433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3775817/10000000) (δ := 41/5000000) (ψ := 80867/500000) 122 99
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t162 : ((23720676571/5000000000000 : ℚ) : ℝ) ≤ stT122 162 := by
  have hc : ((60383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23720676571/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((60383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c163 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((362571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -237361/1250000) (δ := 31/2500000) (ψ := 80867/500000) 122 99
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t163 : ((7099194499/125000000000 : ℚ) : ℝ) ≤ stT122 163 := by
  have hc : ((181273/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7099194499/125000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((181273/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c164 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((999911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33439/10000000) (δ := 23/2500000) (ψ := 80867/500000) 122 99
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t164 : ((195189864837/2500000000000 : ℚ) : ℝ) ≤ stT122 164 := by
  have hc : ((999861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195189864837/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((999861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c165 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((93291/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1820671/10000000) (δ := 903/100000000) (ψ := 80867/500000) 122 99
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t165 : ((145243982611/2500000000000 : ℚ) : ℝ) ≤ stT122 165 := by
  have hc : ((373139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145243982611/2500000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((373139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c166 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((105171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 457947/1250000) (δ := 1043/100000000) (ψ := 80867/500000) 122 99
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t166 : ((1631793283/200000000000 : ℚ) : ℝ) ≤ stT122 166 := by
  have hc : ((105121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1631793283/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((105121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c167 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-587017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2747707/5000000) (δ := 27/2500000) (ψ := 80867/500000) 122 99
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t167 : ((-7098227097/156250000000 : ℚ) : ℝ) ≤ stT122 167 := by
  have hc : ((-587067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7098227097/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-587067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c168 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-488481/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1463263/2000000) (δ := 963/100000000) (ψ := 80867/500000) 122 99
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t168 : ((-188445341801/2500000000000 : ℚ) : ℝ) ≤ stT122 168 := by
  have hc : ((-244253/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188445341801/2500000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-244253/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c169 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-436623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3290777/5000000) (δ := 21/2000000) (ψ := 80867/500000) 122 100
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t169 : ((-41985397211/625000000000 : ℚ) : ℝ) ≤ stT122 169 := by
  have hc : ((-54581/62500 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41985397211/625000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-54581/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c170 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-83857/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4782139/10000000) (δ := 79/10000000) (ψ := 80867/500000) 122 100
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t170 : ((-25729988427/1000000000000 : ℚ) : ℝ) ≤ stT122 170 := by
  have hc : ((-167739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25729988427/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-167739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c171 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((364863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1496639/5000000) (δ := 653/100000000) (ψ := 80867/500000) 122 100
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t171 : ((278979432547/10000000000000 : ℚ) : ℝ) ≤ stT122 171 := by
  have hc : ((364813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((278979432547/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((364813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c172 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((884237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1214847/10000000) (δ := 913/100000000) (ψ := 80867/500000) 122 100
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t172 : ((168546378501/2500000000000 : ℚ) : ℝ) ≤ stT122 172 := by
  have hc : ((884187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168546378501/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((884187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c173 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((975611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 276637/5000000) (δ := 1133/100000000) (ψ := 80867/500000) 122 100
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t173 : ((148340878977/2000000000000 : ℚ) : ℝ) ≤ stT122 173 := by
  have hc : ((975561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148340878977/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((975561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c174 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((602249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 577801/2500000) (δ := 1193/100000000) (ψ := 80867/500000) 122 100
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t174 : ((228262928751/5000000000000 : ℚ) : ℝ) ≤ stT122 174 := by
  have hc : ((602199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228262928751/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((602199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c175 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-52803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 202953/500000) (δ := 893/100000000) (ψ := 80867/500000) 122 100
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t175 : ((-39953115437/10000000000000 : ℚ) : ℝ) ≤ stT122 175 := by
  have hc : ((-52853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39953115437/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-52853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c176 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-170041/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1449239/2500000) (δ := 1133/100000000) (ψ := 80867/500000) 122 100
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t176 : ((-256365514353/5000000000000 : ℚ) : ℝ) ≤ stT122 176 := by
  have hc : ((-340107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256365514353/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-340107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c177 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-495677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3762503/5000000) (δ := 17/2000000) (ψ := 80867/500000) 122 100
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t177 : ((-186296460597/2500000000000 : ℚ) : ℝ) ≤ stT122 177 := by
  have hc : ((-247851/250000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186296460597/2500000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-247851/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c178 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-849513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6464643/10000000) (δ := 639/100000000) (ψ := 80867/500000) 122 101
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t178 : ((-159193663629/2500000000000 : ℚ) : ℝ) ≤ stT122 178 := by
  have hc : ((-849563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159193663629/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-849563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c179 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-325543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -951191/2000000) (δ := 1179/100000000) (ψ := 80867/500000) 122 101
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t179 : ((-60839982387/2500000000000 : ℚ) : ℝ) ≤ stT122 179 := by
  have hc : ((-325593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60839982387/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-325593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c180 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((68219/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1528393/5000000) (δ := 619/100000000) (ψ := 80867/500000) 122 101
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t180 : ((10167983839/400000000000 : ℚ) : ℝ) ≤ stT122 180 := by
  have hc : ((68209/200000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10167983839/400000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((68209/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c181 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((427093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1367031/10000000) (δ := 859/100000000) (ψ := 80867/500000) 122 101
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t181 : ((39679635249/625000000000 : ℚ) : ℝ) ≤ stT122 181 := by
  have hc : ((106767/125000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39679635249/625000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((106767/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c182 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((124019/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156707/5000000) (δ := 261/25000000) (ψ := 80867/500000) 122 101
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t182 : ((367697307699/5000000000000 : ℚ) : ℝ) ≤ stT122 182 := by
  have hc : ((496051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((367697307699/5000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((496051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c183 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((350549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1984651/10000000) (δ := 39/6250000) (ψ := 80867/500000) 122 101
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t183 : ((64778675451/1250000000000 : ℚ) : ℝ) ≤ stT122 183 := by
  have hc : ((87631/125000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64778675451/1250000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((87631/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c184 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((111849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3646781/10000000) (δ := 11/1562500) (ψ := 80867/500000) 122 101
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t184 : ((82419228991/10000000000000 : ℚ) : ℝ) ≤ stT122 184 := by
  have hc : ((111799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82419228991/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((111799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c185 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-260987/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5299901/10000000) (δ := 939/100000000) (ψ := 80867/500000) 122 101
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t185 : ((-9594996879/250000000000 : ℚ) : ℝ) ≤ stT122 185 := by
  have hc : ((-65253/125000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9594996879/250000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-65253/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c186 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-934499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 694411/1000000) (δ := 221/25000000) (ψ := 80867/500000) 122 101
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t186 : ((-171311242641/2500000000000 : ℚ) : ℝ) ≤ stT122 186 := by
  have hc : ((-934549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171311242641/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-934549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c187 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-119773/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7128461/10000000) (δ := 131/12500000) (ψ := 80867/500000) 122 102
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t187 : ((-350365325941/5000000000000 : ℚ) : ℝ) ≤ stT122 187 := by
  have hc : ((-479117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350365325941/5000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-479117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c188 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-14727/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -550179/1000000) (δ := 151/20000000) (ψ := 80867/500000) 122 102
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t188 : ((-1718668949/40000000000 : ℚ) : ℝ) ≤ stT122 188 := by
  have hc : ((-58913/100000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1718668949/40000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-58913/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c189 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((1081/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3883749/10000000) (δ := 131/12500000) (ψ := 80867/500000) 122 102
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t189 : ((196009413/156250000000 : ℚ) : ℝ) ≤ stT122 189 := by
  have hc : ((8623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196009413/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((8623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c190 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((19187/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2274247/10000000) (δ := 171/20000000) (ψ := 80867/500000) 122 102
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t190 : ((55674297823/1250000000000 : ℚ) : ℝ) ≤ stT122 190 := by
  have hc : ((306967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55674297823/1250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((306967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c191 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((963963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -673193/10000000) (δ := 111/12500000) (ψ := 80867/500000) 122 102
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t191 : ((348731192531/5000000000000 : ℚ) : ℝ) ≤ stT122 191 := by
  have hc : ((963913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348731192531/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((963913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c192 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((933121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1839/20000) (δ := 7/800000) (ψ := 80867/500000) 122 102
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t192 : ((673385210777/10000000000000 : ℚ) : ℝ) ≤ stT122 192 := by
  have hc : ((933071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((673385210777/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((933071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c193 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((538983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2503919/10000000) (δ := 43/4000000) (ψ := 80867/500000) 122 102
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t193 : ((77586411479/2000000000000 : ℚ) : ℝ) ≤ stT122 193 := by
  have hc : ((538933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77586411479/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((538933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c194 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-2449/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 81603/200000) (δ := 143/20000000) (ψ := 80867/500000) 122 102
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t194 : ((-1759717509/400000000000 : ℚ) : ℝ) ≤ stT122 194 := by
  have hc : ((-2451/40000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1759717509/400000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-2451/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c195 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-635391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5648277/10000000) (δ := 143/20000000) (ψ := 80867/500000) 122 102
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t195 : ((-91009766343/2000000000000 : ℚ) : ℝ) ≤ stT122 195 := by
  have hc : ((-635441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91009766343/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-635441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c196 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-966841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3604191/5000000) (δ := 139/20000000) (ψ := 80867/500000) 122 102
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t196 : ((-345318352413/5000000000000 : ℚ) : ℝ) ≤ stT122 196 := by
  have hc : ((-966891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-345318352413/5000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-966891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c197 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-116871/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1389483/2000000) (δ := 449/50000000) (ψ := 80867/500000) 122 103
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t197 : ((-333086604739/5000000000000 : ℚ) : ℝ) ≤ stT122 197 := by
  have hc : ((-467509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333086604739/5000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-467509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c198 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-139183/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1350777/2500000) (δ := 439/50000000) (ψ := 80867/500000) 122 103
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t198 : ((-19784413197/500000000000 : ℚ) : ℝ) ≤ stT122 198 := by
  have hc : ((-278391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19784413197/500000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-278391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c199 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((12081/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3866581/10000000) (δ := 479/50000000) (ψ := 80867/500000) 122 103
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t199 : ((1068283667/625000000000 : ℚ) : ℝ) ≤ stT122 199 := by
  have hc : ((1507/62500 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1068283667/625000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((1507/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_c200 :
    |Real.cos (((122 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((74217/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -467551/2000000) (δ := 161/20000000) (ψ := 80867/500000) 122 103
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st122_t200 : ((104949733179/2500000000000 : ℚ) : ℝ) ≤ stT122 200 := by
  have hc : ((296843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((122 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((80867/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st122_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104949733179/2500000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((296843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st122_p1 : ((9869/10000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT122 (i+1) := by
  rw [Finset.sum_range_one]
  exact st122_t1

theorem st122_p2 : ((853595159293/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT122 (i+1))
      = (∑ i ∈ Finset.range 1, stT122 (i+1)) + stT122 2 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 1
    simpa using h
  have hprev := st122_p1
  have hstep := st122_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p3 : ((1427446900231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT122 (i+1))
      = (∑ i ∈ Finset.range 2, stT122 (i+1)) + stT122 3 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 2
    simpa using h
  have hprev := st122_p2
  have hstep := st122_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p4 : ((5315606900231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT122 (i+1))
      = (∑ i ∈ Finset.range 3, stT122 (i+1)) + stT122 4 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 3
    simpa using h
  have hprev := st122_p3
  have hstep := st122_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p5 : ((6027213021431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT122 (i+1))
      = (∑ i ∈ Finset.range 4, stT122 (i+1)) + stT122 5 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 4
    simpa using h
  have hprev := st122_p4
  have hstep := st122_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p6 : ((6403009572013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT122 (i+1))
      = (∑ i ∈ Finset.range 5, stT122 (i+1)) + stT122 6 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 5
    simpa using h
  have hprev := st122_p5
  have hstep := st122_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p7 : ((6588170551929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT122 (i+1))
      = (∑ i ∈ Finset.range 6, stT122 (i+1)) + stT122 7 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 6
    simpa using h
  have hprev := st122_p6
  have hstep := st122_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p8 : ((4499557376963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT122 (i+1))
      = (∑ i ∈ Finset.range 7, stT122 (i+1)) + stT122 8 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 7
    simpa using h
  have hprev := st122_p7
  have hstep := st122_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p9 : ((2335453610809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT122 (i+1))
      = (∑ i ∈ Finset.range 8, stT122 (i+1)) + stT122 9 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 8
    simpa using h
  have hprev := st122_p8
  have hstep := st122_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p10 : ((1049035758131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT122 (i+1))
      = (∑ i ∈ Finset.range 9, stT122 (i+1)) + stT122 10 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 9
    simpa using h
  have hprev := st122_p9
  have hstep := st122_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p11 : ((-1897852242277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT122 (i+1))
      = (∑ i ∈ Finset.range 10, stT122 (i+1)) + stT122 11 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 10
    simpa using h
  have hprev := st122_p10
  have hstep := st122_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p12 : ((-354669389259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT122 (i+1))
      = (∑ i ∈ Finset.range 11, stT122 (i+1)) + stT122 12 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 11
    simpa using h
  have hprev := st122_p11
  have hstep := st122_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p13 : ((-58731401721/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT122 (i+1))
      = (∑ i ∈ Finset.range 12, stT122 (i+1)) + stT122 13 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 12
    simpa using h
  have hprev := st122_p12
  have hstep := st122_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p14 : ((-95684526143/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT122 (i+1))
      = (∑ i ∈ Finset.range 13, stT122 (i+1)) + stT122 14 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 13
    simpa using h
  have hprev := st122_p13
  have hstep := st122_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p15 : ((-1402753085449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT122 (i+1))
      = (∑ i ∈ Finset.range 14, stT122 (i+1)) + stT122 15 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 14
    simpa using h
  have hprev := st122_p14
  have hstep := st122_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p16 : ((-947441835449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT122 (i+1))
      = (∑ i ∈ Finset.range 15, stT122 (i+1)) + stT122 16 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 15
    simpa using h
  have hprev := st122_p15
  have hstep := st122_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p17 : ((52161492899/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT122 (i+1))
      = (∑ i ∈ Finset.range 16, stT122 (i+1)) + stT122 17 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 16
    simpa using h
  have hprev := st122_p16
  have hstep := st122_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p18 : ((1229913558949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT122 (i+1))
      = (∑ i ∈ Finset.range 17, stT122 (i+1)) + stT122 18 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 17
    simpa using h
  have hprev := st122_p17
  have hstep := st122_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p19 : ((3852736011233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT122 (i+1))
      = (∑ i ∈ Finset.range 18, stT122 (i+1)) + stT122 19 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 18
    simpa using h
  have hprev := st122_p18
  have hstep := st122_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p20 : ((65688316321/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT122 (i+1))
      = (∑ i ∈ Finset.range 19, stT122 (i+1)) + stT122 20 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 19
    simpa using h
  have hprev := st122_p19
  have hstep := st122_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p21 : ((55479803439/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT122 (i+1))
      = (∑ i ∈ Finset.range 20, stT122 (i+1)) + stT122 21 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 20
    simpa using h
  have hprev := st122_p20
  have hstep := st122_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p22 : ((9231091556541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT122 (i+1))
      = (∑ i ∈ Finset.range 21, stT122 (i+1)) + stT122 22 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 21
    simpa using h
  have hprev := st122_p21
  have hstep := st122_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p23 : ((2103546349377/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT122 (i+1))
      = (∑ i ∈ Finset.range 22, stT122 (i+1)) + stT122 23 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 22
    simpa using h
  have hprev := st122_p22
  have hstep := st122_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p24 : ((9674384449617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT122 (i+1))
      = (∑ i ∈ Finset.range 23, stT122 (i+1)) + stT122 24 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 23
    simpa using h
  have hprev := st122_p23
  have hstep := st122_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p25 : ((3849592731009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT122 (i+1))
      = (∑ i ∈ Finset.range 24, stT122 (i+1)) + stT122 25 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 24
    simpa using h
  have hprev := st122_p24
  have hstep := st122_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p26 : ((7866419543971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT122 (i+1))
      = (∑ i ∈ Finset.range 25, stT122 (i+1)) + stT122 26 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 25
    simpa using h
  have hprev := st122_p25
  have hstep := st122_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p27 : ((9754908299971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT122 (i+1))
      = (∑ i ∈ Finset.range 26, stT122 (i+1)) + stT122 27 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 26
    simpa using h
  have hprev := st122_p26
  have hstep := st122_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p28 : ((2225142586723/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT122 (i+1))
      = (∑ i ∈ Finset.range 27, stT122 (i+1)) + stT122 28 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 27
    simpa using h
  have hprev := st122_p27
  have hstep := st122_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p29 : ((1936646213283/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT122 (i+1))
      = (∑ i ∈ Finset.range 28, stT122 (i+1)) + stT122 29 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 28
    simpa using h
  have hprev := st122_p28
  have hstep := st122_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p30 : ((74719951847/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT122 (i+1))
      = (∑ i ∈ Finset.range 29, stT122 (i+1)) + stT122 30 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 29
    simpa using h
  have hprev := st122_p29
  have hstep := st122_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p31 : ((4261771748759/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT122 (i+1))
      = (∑ i ∈ Finset.range 30, stT122 (i+1)) + stT122 31 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 30
    simpa using h
  have hprev := st122_p30
  have hstep := st122_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p32 : ((2080664497793/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT122 (i+1))
      = (∑ i ∈ Finset.range 31, stT122 (i+1)) + stT122 32 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 31
    simpa using h
  have hprev := st122_p31
  have hstep := st122_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p33 : ((2369685972267/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT122 (i+1))
      = (∑ i ∈ Finset.range 32, stT122 (i+1)) + stT122 33 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 32
    simpa using h
  have hprev := st122_p32
  have hstep := st122_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p34 : ((983014429977/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT122 (i+1))
      = (∑ i ∈ Finset.range 33, stT122 (i+1)) + stT122 34 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 33
    simpa using h
  have hprev := st122_p33
  have hstep := st122_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p35 : ((477607329747/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT122 (i+1))
      = (∑ i ∈ Finset.range 34, stT122 (i+1)) + stT122 35 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 34
    simpa using h
  have hprev := st122_p34
  have hstep := st122_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p36 : ((79842796147/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT122 (i+1))
      = (∑ i ∈ Finset.range 35, stT122 (i+1)) + stT122 36 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 35
    simpa using h
  have hprev := st122_p35
  have hstep := st122_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p37 : ((9388070313877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT122 (i+1))
      = (∑ i ∈ Finset.range 36, stT122 (i+1)) + stT122 37 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 36
    simpa using h
  have hprev := st122_p36
  have hstep := st122_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p38 : ((8105670423217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT122 (i+1))
      = (∑ i ∈ Finset.range 37, stT122 (i+1)) + stT122 38 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 37
    simpa using h
  have hprev := st122_p37
  have hstep := st122_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p39 : ((4672000133957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT122 (i+1))
      = (∑ i ∈ Finset.range 38, stT122 (i+1)) + stT122 39 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 38
    simpa using h
  have hprev := st122_p38
  have hstep := st122_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p40 : ((8069875770961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT122 (i+1))
      = (∑ i ∈ Finset.range 39, stT122 (i+1)) + stT122 40 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 39
    simpa using h
  have hprev := st122_p39
  have hstep := st122_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p41 : ((1887360964211/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT122 (i+1))
      = (∑ i ∈ Finset.range 40, stT122 (i+1)) + stT122 41 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 40
    simpa using h
  have hprev := st122_p40
  have hstep := st122_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p42 : ((7963997384463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT122 (i+1))
      = (∑ i ∈ Finset.range 41, stT122 (i+1)) + stT122 42 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 41
    simpa using h
  have hprev := st122_p41
  have hstep := st122_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p43 : ((593007357373/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT122 (i+1))
      = (∑ i ∈ Finset.range 42, stT122 (i+1)) + stT122 43 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 42
    simpa using h
  have hprev := st122_p42
  have hstep := st122_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p44 : ((8049936983551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT122 (i+1))
      = (∑ i ∈ Finset.range 43, stT122 (i+1)) + stT122 44 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 43
    simpa using h
  have hprev := st122_p43
  have hstep := st122_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p45 : ((9185569567617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT122 (i+1))
      = (∑ i ∈ Finset.range 44, stT122 (i+1)) + stT122 45 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 44
    simpa using h
  have hprev := st122_p44
  have hstep := st122_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p46 : ((8603182514137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT122 (i+1))
      = (∑ i ∈ Finset.range 45, stT122 (i+1)) + stT122 46 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 45
    simpa using h
  have hprev := st122_p45
  have hstep := st122_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p47 : ((8440330076237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT122 (i+1))
      = (∑ i ∈ Finset.range 46, stT122 (i+1)) + stT122 47 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 46
    simpa using h
  have hprev := st122_p46
  have hstep := st122_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p48 : ((9353336932487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT122 (i+1))
      = (∑ i ∈ Finset.range 47, stT122 (i+1)) + stT122 48 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 47
    simpa using h
  have hprev := st122_p47
  have hstep := st122_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p49 : ((7972653523071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT122 (i+1))
      = (∑ i ∈ Finset.range 48, stT122 (i+1)) + stT122 49 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 48
    simpa using h
  have hprev := st122_p48
  have hstep := st122_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p50 : ((9265603415173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT122 (i+1))
      = (∑ i ∈ Finset.range 49, stT122 (i+1)) + stT122 50 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 49
    simpa using h
  have hprev := st122_p49
  have hstep := st122_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p51 : ((1085524967821/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT122 (i+1))
      = (∑ i ∈ Finset.range 50, stT122 (i+1)) + stT122 51 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 50
    simpa using h
  have hprev := st122_p50
  have hstep := st122_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p52 : ((8215823205567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT122 (i+1))
      = (∑ i ∈ Finset.range 51, stT122 (i+1)) + stT122 52 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 51
    simpa using h
  have hprev := st122_p51
  have hstep := st122_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p53 : ((9476276120087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT122 (i+1))
      = (∑ i ∈ Finset.range 52, stT122 (i+1)) + stT122 53 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 52
    simpa using h
  have hprev := st122_p52
  have hstep := st122_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p54 : ((1650472477199/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT122 (i+1))
      = (∑ i ∈ Finset.range 53, stT122 (i+1)) + stT122 54 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 53
    simpa using h
  have hprev := st122_p53
  have hstep := st122_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p55 : ((8540310295647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT122 (i+1))
      = (∑ i ∈ Finset.range 54, stT122 (i+1)) + stT122 55 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 54
    simpa using h
  have hprev := st122_p54
  have hstep := st122_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p56 : ((9429469599763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT122 (i+1))
      = (∑ i ∈ Finset.range 55, stT122 (i+1)) + stT122 56 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 55
    simpa using h
  have hprev := st122_p55
  have hstep := st122_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p57 : ((8117742184807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT122 (i+1))
      = (∑ i ∈ Finset.range 56, stT122 (i+1)) + stT122 57 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 56
    simpa using h
  have hprev := st122_p56
  have hstep := st122_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p58 : ((1728569133971/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT122 (i+1))
      = (∑ i ∈ Finset.range 57, stT122 (i+1)) + stT122 58 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 57
    simpa using h
  have hprev := st122_p57
  have hstep := st122_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p59 : ((377002385509/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT122 (i+1))
      = (∑ i ∈ Finset.range 58, stT122 (i+1)) + stT122 59 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 58
    simpa using h
  have hprev := st122_p58
  have hstep := st122_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p60 : ((65212151121/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT122 (i+1))
      = (∑ i ∈ Finset.range 59, stT122 (i+1)) + stT122 60 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 59
    simpa using h
  have hprev := st122_p59
  have hstep := st122_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p61 : ((8506337031021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT122 (i+1))
      = (∑ i ∈ Finset.range 60, stT122 (i+1)) + stT122 61 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 60
    simpa using h
  have hprev := st122_p60
  have hstep := st122_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p62 : ((9482647759769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT122 (i+1))
      = (∑ i ∈ Finset.range 61, stT122 (i+1)) + stT122 62 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 61
    simpa using h
  have hprev := st122_p61
  have hstep := st122_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p63 : ((8374356021891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT122 (i+1))
      = (∑ i ∈ Finset.range 62, stT122 (i+1)) + stT122 63 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 62
    simpa using h
  have hprev := st122_p62
  have hstep := st122_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p64 : ((8193415877139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT122 (i+1))
      = (∑ i ∈ Finset.range 63, stT122 (i+1)) + stT122 64 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 63
    simpa using h
  have hprev := st122_p63
  have hstep := st122_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p65 : ((4707323944761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT122 (i+1))
      = (∑ i ∈ Finset.range 64, stT122 (i+1)) + stT122 65 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 64
    simpa using h
  have hprev := st122_p64
  have hstep := st122_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p66 : ((8860045596207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT122 (i+1))
      = (∑ i ∈ Finset.range 65, stT122 (i+1)) + stT122 66 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 65
    simpa using h
  have hprev := st122_p65
  have hstep := st122_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p67 : ((496909748447/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT122 (i+1))
      = (∑ i ∈ Finset.range 66, stT122 (i+1)) + stT122 67 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 66
    simpa using h
  have hprev := st122_p66
  have hstep := st122_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p68 : ((2237327574971/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT122 (i+1))
      = (∑ i ∈ Finset.range 67, stT122 (i+1)) + stT122 68 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 67
    simpa using h
  have hprev := st122_p67
  have hstep := st122_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p69 : ((2352495854399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT122 (i+1))
      = (∑ i ∈ Finset.range 68, stT122 (i+1)) + stT122 69 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 68
    simpa using h
  have hprev := st122_p68
  have hstep := st122_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p70 : ((8240481721821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT122 (i+1))
      = (∑ i ∈ Finset.range 69, stT122 (i+1)) + stT122 70 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 69
    simpa using h
  have hprev := st122_p69
  have hstep := st122_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p71 : ((8183036725893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT122 (i+1))
      = (∑ i ∈ Finset.range 70, stT122 (i+1)) + stT122 71 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 70
    simpa using h
  have hprev := st122_p70
  have hstep := st122_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p72 : ((4678508175549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT122 (i+1))
      = (∑ i ∈ Finset.range 71, stT122 (i+1)) + stT122 72 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 71
    simpa using h
  have hprev := st122_p71
  have hstep := st122_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p73 : ((4562709367887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT122 (i+1))
      = (∑ i ∈ Finset.range 72, stT122 (i+1)) + stT122 73 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 72
    simpa using h
  have hprev := st122_p72
  have hstep := st122_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p74 : ((1602167855121/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT122 (i+1))
      = (∑ i ∈ Finset.range 73, stT122 (i+1)) + stT122 74 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 73
    simpa using h
  have hprev := st122_p73
  have hstep := st122_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p75 : ((1682438904081/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT122 (i+1))
      = (∑ i ∈ Finset.range 74, stT122 (i+1)) + stT122 75 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 74
    simpa using h
  have hprev := st122_p74
  have hstep := st122_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p76 : ((9468591416193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT122 (i+1))
      = (∑ i ∈ Finset.range 75, stT122 (i+1)) + stT122 76 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 75
    simpa using h
  have hprev := st122_p75
  have hstep := st122_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p77 : ((8999518190533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT122 (i+1))
      = (∑ i ∈ Finset.range 76, stT122 (i+1)) + stT122 77 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 76
    simpa using h
  have hprev := st122_p76
  have hstep := st122_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p78 : ((7969122564973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT122 (i+1))
      = (∑ i ∈ Finset.range 77, stT122 (i+1)) + stT122 78 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 77
    simpa using h
  have hprev := st122_p77
  have hstep := st122_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p79 : ((8418516065383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT122 (i+1))
      = (∑ i ∈ Finset.range 78, stT122 (i+1)) + stT122 79 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 78
    simpa using h
  have hprev := st122_p78
  have hstep := st122_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p80 : ((1891778993067/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT122 (i+1))
      = (∑ i ∈ Finset.range 79, stT122 (i+1)) + stT122 80 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 79
    simpa using h
  have hprev := st122_p79
  have hstep := st122_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p81 : ((9109832463863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT122 (i+1))
      = (∑ i ∈ Finset.range 80, stT122 (i+1)) + stT122 81 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 80
    simpa using h
  have hprev := st122_p80
  have hstep := st122_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p82 : ((8038618335963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT122 (i+1))
      = (∑ i ∈ Finset.range 81, stT122 (i+1)) + stT122 82 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 81
    simpa using h
  have hprev := st122_p81
  have hstep := st122_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p83 : ((1641317220131/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT122 (i+1))
      = (∑ i ∈ Finset.range 82, stT122 (i+1)) + stT122 83 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 82
    simpa using h
  have hprev := st122_p82
  have hstep := st122_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p84 : ((4648282731571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT122 (i+1))
      = (∑ i ∈ Finset.range 83, stT122 (i+1)) + stT122 84 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 83
    simpa using h
  have hprev := st122_p83
  have hstep := st122_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p85 : ((4693224202539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT122 (i+1))
      = (∑ i ∈ Finset.range 84, stT122 (i+1)) + stT122 85 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 84
    simpa using h
  have hprev := st122_p84
  have hstep := st122_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p86 : ((4167852017659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT122 (i+1))
      = (∑ i ∈ Finset.range 85, stT122 (i+1)) + stT122 86 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 85
    simpa using h
  have hprev := st122_p85
  have hstep := st122_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p87 : ((317230206479/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT122 (i+1))
      = (∑ i ∈ Finset.range 86, stT122 (i+1)) + stT122 87 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 86
    simpa using h
  have hprev := st122_p86
  have hstep := st122_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p88 : ((353269635903/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT122 (i+1))
      = (∑ i ∈ Finset.range 87, stT122 (i+1)) + stT122 88 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 87
    simpa using h
  have hprev := st122_p87
  have hstep := st122_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p89 : ((9558875519641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT122 (i+1))
      = (∑ i ∈ Finset.range 88, stT122 (i+1)) + stT122 89 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 88
    simpa using h
  have hprev := st122_p88
  have hstep := st122_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p90 : ((2239362790867/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT122 (i+1))
      = (∑ i ∈ Finset.range 89, stT122 (i+1)) + stT122 90 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 89
    simpa using h
  have hprev := st122_p89
  have hstep := st122_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p91 : ((7985618636803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT122 (i+1))
      = (∑ i ∈ Finset.range 90, stT122 (i+1)) + stT122 91 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 90
    simpa using h
  have hprev := st122_p90
  have hstep := st122_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p92 : ((8138233453879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT122 (i+1))
      = (∑ i ∈ Finset.range 91, stT122 (i+1)) + stT122 92 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 91
    simpa using h
  have hprev := st122_p91
  have hstep := st122_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p93 : ((4584716243341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT122 (i+1))
      = (∑ i ∈ Finset.range 92, stT122 (i+1)) + stT122 93 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 92
    simpa using h
  have hprev := st122_p92
  have hstep := st122_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p94 : ((4771599414331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT122 (i+1))
      = (∑ i ∈ Finset.range 93, stT122 (i+1)) + stT122 94 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 93
    simpa using h
  have hprev := st122_p93
  have hstep := st122_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p95 : ((218169708779/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT122 (i+1))
      = (∑ i ∈ Finset.range 94, stT122 (i+1)) + stT122 95 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 94
    simpa using h
  have hprev := st122_p94
  have hstep := st122_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p96 : ((1975038685847/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT122 (i+1))
      = (∑ i ∈ Finset.range 95, stT122 (i+1)) + stT122 96 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 95
    simpa using h
  have hprev := st122_p95
  have hstep := st122_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p97 : ((513737238603/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT122 (i+1))
      = (∑ i ∈ Finset.range 96, stT122 (i+1)) + stT122 97 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 96
    simpa using h
  have hprev := st122_p96
  have hstep := st122_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p98 : ((288434290939/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT122 (i+1))
      = (∑ i ∈ Finset.range 97, stT122 (i+1)) + stT122 98 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 97
    simpa using h
  have hprev := st122_p97
  have hstep := st122_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p99 : ((4778426968407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT122 (i+1))
      = (∑ i ∈ Finset.range 98, stT122 (i+1)) + stT122 99 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 98
    simpa using h
  have hprev := st122_p98
  have hstep := st122_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p100 : ((4388378968407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT122 (i+1))
      = (∑ i ∈ Finset.range 99, stT122 (i+1)) + stT122 100 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 99
    simpa using h
  have hprev := st122_p99
  have hstep := st122_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p101 : ((990271815713/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT122 (i+1))
      = (∑ i ∈ Finset.range 100, stT122 (i+1)) + stT122 101 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 100
    simpa using h
  have hprev := st122_p100
  have hstep := st122_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p102 : ((1617746024603/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT122 (i+1))
      = (∑ i ∈ Finset.range 101, stT122 (i+1)) + stT122 102 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 101
    simpa using h
  have hprev := st122_p101
  have hstep := st122_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p103 : ((9052058697103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT122 (i+1))
      = (∑ i ∈ Finset.range 102, stT122 (i+1)) + stT122 103 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 102
    simpa using h
  have hprev := st122_p102
  have hstep := st122_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p104 : ((9608530983043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT122 (i+1))
      = (∑ i ∈ Finset.range 103, stT122 (i+1)) + stT122 104 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 103
    simpa using h
  have hprev := st122_p103
  have hstep := st122_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p105 : ((9086831874661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT122 (i+1))
      = (∑ i ∈ Finset.range 104, stT122 (i+1)) + stT122 105 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 104
    simpa using h
  have hprev := st122_p104
  have hstep := st122_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p106 : ((1625268149453/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT122 (i+1))
      = (∑ i ∈ Finset.range 105, stT122 (i+1)) + stT122 106 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 105
    simpa using h
  have hprev := st122_p105
  have hstep := st122_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p107 : ((7863142732067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT122 (i+1))
      = (∑ i ∈ Finset.range 106, stT122 (i+1)) + stT122 107 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 106
    simpa using h
  have hprev := st122_p106
  have hstep := st122_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p108 : ((8591831563067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT122 (i+1))
      = (∑ i ∈ Finset.range 107, stT122 (i+1)) + stT122 108 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 107
    simpa using h
  have hprev := st122_p107
  have hstep := st122_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p109 : ((378765440189/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT122 (i+1))
      = (∑ i ∈ Finset.range 108, stT122 (i+1)) + stT122 109 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 108
    simpa using h
  have hprev := st122_p108
  have hstep := st122_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p110 : ((380433045227/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT122 (i+1))
      = (∑ i ∈ Finset.range 109, stT122 (i+1)) + stT122 110 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 109
    simpa using h
  have hprev := st122_p109
  have hstep := st122_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p111 : ((8682640216091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT122 (i+1))
      = (∑ i ∈ Finset.range 110, stT122 (i+1)) + stT122 111 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 110
    simpa using h
  have hprev := st122_p110
  have hstep := st122_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p112 : ((7894116821563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT122 (i+1))
      = (∑ i ∈ Finset.range 111, stT122 (i+1)) + stT122 112 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 111
    simpa using h
  have hprev := st122_p111
  have hstep := st122_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p113 : ((7985483310843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT122 (i+1))
      = (∑ i ∈ Finset.range 112, stT122 (i+1)) + stT122 113 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 112
    simpa using h
  have hprev := st122_p112
  have hstep := st122_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p114 : ((8848608202953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT122 (i+1))
      = (∑ i ∈ Finset.range 113, stT122 (i+1)) + stT122 114 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 113
    simpa using h
  have hprev := st122_p113
  have hstep := st122_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p115 : ((9581248620633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT122 (i+1))
      = (∑ i ∈ Finset.range 114, stT122 (i+1)) + stT122 115 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 114
    simpa using h
  have hprev := st122_p114
  have hstep := st122_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p116 : ((295007090359/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT122 (i+1))
      = (∑ i ∈ Finset.range 115, stT122 (i+1)) + stT122 116 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 115
    simpa using h
  have hprev := st122_p115
  have hstep := st122_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p117 : ((8578629864029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT122 (i+1))
      = (∑ i ∈ Finset.range 116, stT122 (i+1)) + stT122 117 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 116
    simpa using h
  have hprev := st122_p116
  have hstep := st122_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p118 : ((1963847560401/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT122 (i+1))
      = (∑ i ∈ Finset.range 117, stT122 (i+1)) + stT122 118 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 117
    simpa using h
  have hprev := st122_p117
  have hstep := st122_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p119 : ((398522342049/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT122 (i+1))
      = (∑ i ∈ Finset.range 118, stT122 (i+1)) + stT122 119 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 118
    simpa using h
  have hprev := st122_p118
  have hstep := st122_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p120 : ((176048932011/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT122 (i+1))
      = (∑ i ∈ Finset.range 119, stT122 (i+1)) + stT122 120 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 119
    simpa using h
  have hprev := st122_p119
  have hstep := st122_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p121 : ((955856948079/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT122 (i+1))
      = (∑ i ∈ Finset.range 120, stT122 (i+1)) + stT122 121 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 120
    simpa using h
  have hprev := st122_p120
  have hstep := st122_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p122 : ((4769392798887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT122 (i+1))
      = (∑ i ∈ Finset.range 121, stT122 (i+1)) + stT122 122 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 121
    simpa using h
  have hprev := st122_p121
  have hstep := st122_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p123 : ((4385747542277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT122 (i+1))
      = (∑ i ∈ Finset.range 122, stT122 (i+1)) + stT122 123 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 122
    simpa using h
  have hprev := st122_p122
  have hstep := st122_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p124 : ((3978488705669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT122 (i+1))
      = (∑ i ∈ Finset.range 123, stT122 (i+1)) + stT122 124 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 123
    simpa using h
  have hprev := st122_p123
  have hstep := st122_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p125 : ((3908947823097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT122 (i+1))
      = (∑ i ∈ Finset.range 124, stT122 (i+1)) + stT122 125 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 124
    simpa using h
  have hprev := st122_p124
  have hstep := st122_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p126 : ((4233396441007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT122 (i+1))
      = (∑ i ∈ Finset.range 125, stT122 (i+1)) + stT122 126 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 125
    simpa using h
  have hprev := st122_p125
  have hstep := st122_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p127 : ((4667335265229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT122 (i+1))
      = (∑ i ∈ Finset.range 126, stT122 (i+1)) + stT122 127 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 126
    simpa using h
  have hprev := st122_p126
  have hstep := st122_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p128 : ((2420572334999/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT122 (i+1))
      = (∑ i ∈ Finset.range 127, stT122 (i+1)) + stT122 128 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 127
    simpa using h
  have hprev := st122_p127
  have hstep := st122_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p129 : ((2306420101947/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT122 (i+1))
      = (∑ i ∈ Finset.range 128, stT122 (i+1)) + stT122 129 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 128
    simpa using h
  have hprev := st122_p128
  have hstep := st122_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p130 : ((835163673663/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT122 (i+1))
      = (∑ i ∈ Finset.range 129, stT122 (i+1)) + stT122 130 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 129
    simpa using h
  have hprev := st122_p129
  have hstep := st122_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p131 : ((1555166912391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT122 (i+1))
      = (∑ i ∈ Finset.range 130, stT122 (i+1)) + stT122 131 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 130
    simpa using h
  have hprev := st122_p130
  have hstep := st122_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p132 : ((7955777706687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT122 (i+1))
      = (∑ i ∈ Finset.range 131, stT122 (i+1)) + stT122 132 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 131
    simpa using h
  have hprev := st122_p131
  have hstep := st122_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p133 : ((8739606957/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT122 (i+1))
      = (∑ i ∈ Finset.range 132, stT122 (i+1)) + stT122 133 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 132
    simpa using h
  have hprev := st122_p132
  have hstep := st122_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p134 : ((2377232662869/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT122 (i+1))
      = (∑ i ∈ Finset.range 133, stT122 (i+1)) + stT122 134 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 133
    simpa using h
  have hprev := st122_p133
  have hstep := st122_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p135 : ((483639690549/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT122 (i+1))
      = (∑ i ∈ Finset.range 134, stT122 (i+1)) + stT122 135 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 134
    simpa using h
  have hprev := st122_p134
  have hstep := st122_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p136 : ((2278653471897/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT122 (i+1))
      = (∑ i ∈ Finset.range 135, stT122 (i+1)) + stT122 136 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 135
    simpa using h
  have hprev := st122_p135
  have hstep := st122_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p137 : ((206516094153/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT122 (i+1))
      = (∑ i ∈ Finset.range 136, stT122 (i+1)) + stT122 137 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 136
    simpa using h
  have hprev := st122_p136
  have hstep := st122_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p138 : ((7744227855813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT122 (i+1))
      = (∑ i ∈ Finset.range 137, stT122 (i+1)) + stT122 138 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 137
    simpa using h
  have hprev := st122_p137
  have hstep := st122_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p139 : ((1587360770417/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT122 (i+1))
      = (∑ i ∈ Finset.range 138, stT122 (i+1)) + stT122 139 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 138
    simpa using h
  have hprev := st122_p138
  have hstep := st122_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p140 : ((8691362414209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT122 (i+1))
      = (∑ i ∈ Finset.range 139, stT122 (i+1)) + stT122 140 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 139
    simpa using h
  have hprev := st122_p139
  have hstep := st122_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p141 : ((9466604517259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT122 (i+1))
      = (∑ i ∈ Finset.range 140, stT122 (i+1)) + stT122 141 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 140
    simpa using h
  have hprev := st122_p140
  have hstep := st122_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p142 : ((9720498728809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT122 (i+1))
      = (∑ i ∈ Finset.range 141, stT122 (i+1)) + stT122 142 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 141
    simpa using h
  have hprev := st122_p141
  have hstep := st122_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p143 : ((9284272567859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT122 (i+1))
      = (∑ i ∈ Finset.range 142, stT122 (i+1)) + stT122 143 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 142
    simpa using h
  have hprev := st122_p142
  have hstep := st122_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p144 : ((8463177744317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT122 (i+1))
      = (∑ i ∈ Finset.range 143, stT122 (i+1)) + stT122 144 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 143
    simpa using h
  have hprev := st122_p143
  have hstep := st122_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p145 : ((122085112373/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT122 (i+1))
      = (∑ i ∈ Finset.range 144, stT122 (i+1)) + stT122 145 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 144
    simpa using h
  have hprev := st122_p144
  have hstep := st122_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p146 : ((3881928933979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT122 (i+1))
      = (∑ i ∈ Finset.range 145, stT122 (i+1)) + stT122 146 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 145
    simpa using h
  have hprev := st122_p145
  have hstep := st122_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p147 : ((4169836158213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT122 (i+1))
      = (∑ i ∈ Finset.range 146, stT122 (i+1)) + stT122 147 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 146
    simpa using h
  have hprev := st122_p146
  have hstep := st122_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p148 : ((4580637523641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT122 (i+1))
      = (∑ i ∈ Finset.range 147, stT122 (i+1)) + stT122 148 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 147
    simpa using h
  have hprev := st122_p147
  have hstep := st122_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p149 : ((9701457126369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT122 (i+1))
      = (∑ i ∈ Finset.range 148, stT122 (i+1)) + stT122 149 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 148
    simpa using h
  have hprev := st122_p148
  have hstep := st122_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p150 : ((4811576307289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT122 (i+1))
      = (∑ i ∈ Finset.range 149, stT122 (i+1)) + stT122 150 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 149
    simpa using h
  have hprev := st122_p149
  have hstep := st122_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p151 : ((4491153398851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT122 (i+1))
      = (∑ i ∈ Finset.range 150, stT122 (i+1)) + stT122 151 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 150
    simpa using h
  have hprev := st122_p150
  have hstep := st122_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p152 : ((817922146693/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT122 (i+1))
      = (∑ i ∈ Finset.range 151, stT122 (i+1)) + stT122 152 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 151
    simpa using h
  have hprev := st122_p151
  have hstep := st122_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p153 : ((7703100050093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT122 (i+1))
      = (∑ i ∈ Finset.range 152, stT122 (i+1)) + stT122 153 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 152
    simpa using h
  have hprev := st122_p152
  have hstep := st122_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p154 : ((7835512721133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT122 (i+1))
      = (∑ i ∈ Finset.range 153, stT122 (i+1)) + stT122 154 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 153
    simpa using h
  have hprev := st122_p153
  have hstep := st122_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p155 : ((66336273753/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT122 (i+1))
      = (∑ i ∈ Finset.range 154, stT122 (i+1)) + stT122 155 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 154
    simpa using h
  have hprev := st122_p154
  have hstep := st122_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p156 : ((18125583477/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT122 (i+1))
      = (∑ i ∈ Finset.range 155, stT122 (i+1)) + stT122 156 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 155
    simpa using h
  have hprev := st122_p155
  have hstep := st122_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p157 : ((2436432032469/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT122 (i+1))
      = (∑ i ∈ Finset.range 156, stT122 (i+1)) + stT122 157 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 156
    simpa using h
  have hprev := st122_p156
  have hstep := st122_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p158 : ((1203163064427/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT122 (i+1))
      = (∑ i ∈ Finset.range 157, stT122 (i+1)) + stT122 158 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 157
    simpa using h
  have hprev := st122_p157
  have hstep := st122_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p159 : ((17987066243/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT122 (i+1))
      = (∑ i ∈ Finset.range 158, stT122 (i+1)) + stT122 159 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 158
    simpa using h
  have hprev := st122_p158
  have hstep := st122_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p160 : ((205205273129/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT122 (i+1))
      = (∑ i ∈ Finset.range 159, stT122 (i+1)) + stT122 160 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 159
    simpa using h
  have hprev := st122_p159
  have hstep := st122_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p161 : ((3851753108491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT122 (i+1))
      = (∑ i ∈ Finset.range 160, stT122 (i+1)) + stT122 161 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 160
    simpa using h
  have hprev := st122_p160
  have hstep := st122_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p162 : ((1937736892531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT122 (i+1))
      = (∑ i ∈ Finset.range 161, stT122 (i+1)) + stT122 162 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 161
    simpa using h
  have hprev := st122_p161
  have hstep := st122_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p163 : ((2079720782511/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT122 (i+1))
      = (∑ i ∈ Finset.range 162, stT122 (i+1)) + stT122 163 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 162
    simpa using h
  have hprev := st122_p162
  have hstep := st122_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p164 : ((568727661837/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT122 (i+1))
      = (∑ i ∈ Finset.range 163, stT122 (i+1)) + stT122 164 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 163
    simpa using h
  have hprev := st122_p163
  have hstep := st122_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p165 : ((2420154629959/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT122 (i+1))
      = (∑ i ∈ Finset.range 164, stT122 (i+1)) + stT122 165 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 164
    simpa using h
  have hprev := st122_p164
  have hstep := st122_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p166 : ((4881104091993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT122 (i+1))
      = (∑ i ∈ Finset.range 165, stT122 (i+1)) + stT122 166 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 165
    simpa using h
  have hprev := st122_p165
  have hstep := st122_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p167 : ((4653960824889/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT122 (i+1))
      = (∑ i ∈ Finset.range 166, stT122 (i+1)) + stT122 167 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 166
    simpa using h
  have hprev := st122_p166
  have hstep := st122_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p168 : ((4277070141287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT122 (i+1))
      = (∑ i ∈ Finset.range 167, stT122 (i+1)) + stT122 168 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 167
    simpa using h
  have hprev := st122_p167
  have hstep := st122_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p169 : ((3941186963599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT122 (i+1))
      = (∑ i ∈ Finset.range 168, stT122 (i+1)) + stT122 169 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 168
    simpa using h
  have hprev := st122_p168
  have hstep := st122_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p170 : ((476567127683/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT122 (i+1))
      = (∑ i ∈ Finset.range 169, stT122 (i+1)) + stT122 170 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 169
    simpa using h
  have hprev := st122_p169
  have hstep := st122_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p171 : ((316162139019/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT122 (i+1))
      = (∑ i ∈ Finset.range 170, stT122 (i+1)) + stT122 171 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 170
    simpa using h
  have hprev := st122_p170
  have hstep := st122_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p172 : ((8578238989479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT122 (i+1))
      = (∑ i ∈ Finset.range 171, stT122 (i+1)) + stT122 172 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 171
    simpa using h
  have hprev := st122_p171
  have hstep := st122_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p173 : ((2329985846091/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT122 (i+1))
      = (∑ i ∈ Finset.range 172, stT122 (i+1)) + stT122 173 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 172
    simpa using h
  have hprev := st122_p172
  have hstep := st122_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p174 : ((4888234620933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT122 (i+1))
      = (∑ i ∈ Finset.range 173, stT122 (i+1)) + stT122 174 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 173
    simpa using h
  have hprev := st122_p173
  have hstep := st122_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p175 : ((9736516126429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT122 (i+1))
      = (∑ i ∈ Finset.range 174, stT122 (i+1)) + stT122 175 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 174
    simpa using h
  have hprev := st122_p174
  have hstep := st122_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p176 : ((9223785097723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT122 (i+1))
      = (∑ i ∈ Finset.range 175, stT122 (i+1)) + stT122 176 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 175
    simpa using h
  have hprev := st122_p175
  have hstep := st122_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p177 : ((1695719851067/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT122 (i+1))
      = (∑ i ∈ Finset.range 176, stT122 (i+1)) + stT122 177 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 176
    simpa using h
  have hprev := st122_p176
  have hstep := st122_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p178 : ((7841824600819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT122 (i+1))
      = (∑ i ∈ Finset.range 177, stT122 (i+1)) + stT122 178 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 177
    simpa using h
  have hprev := st122_p177
  have hstep := st122_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p179 : ((7598464671271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT122 (i+1))
      = (∑ i ∈ Finset.range 178, stT122 (i+1)) + stT122 179 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 178
    simpa using h
  have hprev := st122_p178
  have hstep := st122_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p180 : ((3926332133623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT122 (i+1))
      = (∑ i ∈ Finset.range 179, stT122 (i+1)) + stT122 180 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 179
    simpa using h
  have hprev := st122_p179
  have hstep := st122_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p181 : ((848753843123/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT122 (i+1))
      = (∑ i ∈ Finset.range 180, stT122 (i+1)) + stT122 181 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 180
    simpa using h
  have hprev := st122_p180
  have hstep := st122_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p182 : ((2305733261657/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT122 (i+1))
      = (∑ i ∈ Finset.range 181, stT122 (i+1)) + stT122 182 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 181
    simpa using h
  have hprev := st122_p181
  have hstep := st122_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p183 : ((2435290612559/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT122 (i+1))
      = (∑ i ∈ Finset.range 182, stT122 (i+1)) + stT122 183 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 182
    simpa using h
  have hprev := st122_p182
  have hstep := st122_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p184 : ((9823581679227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT122 (i+1))
      = (∑ i ∈ Finset.range 183, stT122 (i+1)) + stT122 184 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 183
    simpa using h
  have hprev := st122_p183
  have hstep := st122_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p185 : ((9439781804067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT122 (i+1))
      = (∑ i ∈ Finset.range 184, stT122 (i+1)) + stT122 185 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 184
    simpa using h
  have hprev := st122_p184
  have hstep := st122_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p186 : ((8754536833503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT122 (i+1))
      = (∑ i ∈ Finset.range 185, stT122 (i+1)) + stT122 186 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 185
    simpa using h
  have hprev := st122_p185
  have hstep := st122_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p187 : ((8053806181621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT122 (i+1))
      = (∑ i ∈ Finset.range 186, stT122 (i+1)) + stT122 187 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 186
    simpa using h
  have hprev := st122_p186
  have hstep := st122_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p188 : ((7624138944371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT122 (i+1))
      = (∑ i ∈ Finset.range 187, stT122 (i+1)) + stT122 188 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 187
    simpa using h
  have hprev := st122_p187
  have hstep := st122_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p189 : ((7636683546803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT122 (i+1))
      = (∑ i ∈ Finset.range 188, stT122 (i+1)) + stT122 189 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 188
    simpa using h
  have hprev := st122_p188
  have hstep := st122_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p190 : ((8082077929387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT122 (i+1))
      = (∑ i ∈ Finset.range 189, stT122 (i+1)) + stT122 190 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 189
    simpa using h
  have hprev := st122_p189
  have hstep := st122_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p191 : ((8779540314449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT122 (i+1))
      = (∑ i ∈ Finset.range 190, stT122 (i+1)) + stT122 191 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 190
    simpa using h
  have hprev := st122_p190
  have hstep := st122_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p192 : ((4726462762613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT122 (i+1))
      = (∑ i ∈ Finset.range 191, stT122 (i+1)) + stT122 192 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 191
    simpa using h
  have hprev := st122_p191
  have hstep := st122_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p193 : ((9840857582621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT122 (i+1))
      = (∑ i ∈ Finset.range 192, stT122 (i+1)) + stT122 193 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 192
    simpa using h
  have hprev := st122_p192
  have hstep := st122_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p194 : ((306152020153/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT122 (i+1))
      = (∑ i ∈ Finset.range 193, stT122 (i+1)) + stT122 194 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 193
    simpa using h
  have hprev := st122_p193
  have hstep := st122_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p195 : ((9341815813181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT122 (i+1))
      = (∑ i ∈ Finset.range 194, stT122 (i+1)) + stT122 195 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 194
    simpa using h
  have hprev := st122_p194
  have hstep := st122_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p196 : ((1730235821671/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT122 (i+1))
      = (∑ i ∈ Finset.range 195, stT122 (i+1)) + stT122 196 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 195
    simpa using h
  have hprev := st122_p195
  have hstep := st122_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p197 : ((7985005898877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT122 (i+1))
      = (∑ i ∈ Finset.range 196, stT122 (i+1)) + stT122 197 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 196
    simpa using h
  have hprev := st122_p196
  have hstep := st122_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p198 : ((7589317634937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT122 (i+1))
      = (∑ i ∈ Finset.range 197, stT122 (i+1)) + stT122 198 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 197
    simpa using h
  have hprev := st122_p197
  have hstep := st122_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p199 : ((7606410173609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT122 (i+1))
      = (∑ i ∈ Finset.range 198, stT122 (i+1)) + stT122 199 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 198
    simpa using h
  have hprev := st122_p198
  have hstep := st122_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_p200 : ((321048364253/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT122 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT122 (i+1))
      = (∑ i ∈ Finset.range 199, stT122 (i+1)) + stT122 200 := by
    have h := Finset.sum_range_succ (fun i => stT122 (i+1)) 199
    simpa using h
  have hprev := st122_p199
  have hstep := st122_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st122_s200 :
    |Real.sin (((122 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((80867/500000 : ℚ) : ℝ))
      - ((-40233/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -467551/2000000) (δ := 161/20000000) (ψ := 80867/500000) 122 103
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 122`** (evaluated boundary). -/
theorem station_122_sign : 0 < hardyG ((((122:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 122 200 (by norm_num) (by norm_num)
    ((80867/500000 : ℚ) : ℝ)
  have hchain := st122_p200
  have hbridge : (∑ i ∈ Finset.range 200, stT122 (i+1))
      = ∑ i ∈ Finset.range 200,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((122 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((80867/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_200
  have hsh := rpow_half_shifts (N := 200) (by norm_num)
  have hcosb := abs_le.mp st122_c200
  have hsinb := abs_le.mp st122_s200
  have hbdy_lo : ((34600650667431/372106250000000 : ℚ) : ℝ)
      ≤ ((200:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((122 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((80867/500000 : ℚ) : ℝ))) / 2
          - ((((122:ℕ)):ℝ))
            * Real.sin (((122 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((80867/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((122:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((122:ℝ) * Real.log (200:ℝ) - ((80867/500000 : ℚ) : ℝ))) / 2
        - ((122:ℝ)) * Real.sin ((122:ℝ) * Real.log (200:ℝ) - ((80867/500000 : ℚ) : ℝ))
        ≥ ((97865527/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (200:ℝ) * ((200:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (200:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((122:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((97865527/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (200:ℝ) * (353553/5000000)
          * ((97865527/1000000 : ℚ) : ℝ)
        ≤ (200:ℝ) * ((200:ℝ) ^ (-(1/2:ℝ)))
          * ((97865527/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((200:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((122:ℕ)):ℝ))+1) * (((((122:ℕ)):ℝ))+2) / 8
        * (((200:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((200:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((390473677791/800000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((321048364253/400000000000 : ℚ) : ℝ) + ((34600650667431/372106250000000 : ℚ) : ℝ)
      - ((390473677791/800000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((80867/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((122:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((80867/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((122:ℕ)):ℝ)))).re
      - Real.sin ((80867/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((122:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((122:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((122:ℕ)):ℝ))
      = (((((122:ℕ)):ℝ)) * (Real.log ((((122:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((122:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_122
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
  have hθwin : |(((80867/500000 : ℚ) : ℝ) + ((19:ℤ)) * (2*Real.pi)) - theta ((((122:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((122:ℕ)):ℝ)))
    (φ := ((80867/500000 : ℚ) : ℝ) + ((19:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((80867/500000 : ℚ)) : ℝ) 19).1,
    (cos_sin_shift (((80867/500000 : ℚ)) : ℝ) 19).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_122_sign
end AxiomAudit
